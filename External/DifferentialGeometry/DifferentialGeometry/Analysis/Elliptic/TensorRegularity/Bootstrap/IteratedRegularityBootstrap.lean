import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Bootstrap.BootstrapSourceHeadline

noncomputable section

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

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
open DifferentialGeometry.Analysis.Sobolev.NirenbergIteration
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

section GenericEuclidean

variable {d : ℕ} [NeZero d]

local notation "EE" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem wkpNorm_assembly_le
    (m : ℕ) {Ω : Set EE} (hΩ : IsOpen Ω) :
    ∃ N : ℝ≥0∞, N ≠ (⊤ : ℝ≥0∞) ∧
      ∀ {u : EE → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
      iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω ≤
        (∑ idx : Fin m → Fin d,
          iteratedWeakSobolevNorm (d := d) 2 2 (iterClassicalPartial (d := d) m idx u) Ω) +
        N * iteratedWeakSobolevNorm (d := d) (m + 1) 2 u Ω := by
  classical
  induction m with
  | zero =>
      refine ⟨0, by norm_num, fun {u} _hu_cd _hu_cpt => ?_⟩
      have hUniq : ∀ idx : Fin 0 → Fin d, idx = (fun i : Fin 0 => i.elim0) :=
        fun idx => by funext i; exact i.elim0
      haveI : Unique (Fin 0 → Fin d) :=
        { default := fun i : Fin 0 => i.elim0
          uniq := fun idx => (hUniq idx).symm ▸ rfl }
      have h_sum :
          (∑ idx : Fin 0 → Fin d,
            iteratedWeakSobolevNorm (d := d) 2 2 (iterClassicalPartial (d := d) 0 idx u) Ω) =
            iteratedWeakSobolevNorm (d := d) 2 2 u Ω := by
        rw [Fintype.sum_unique
              (f := fun idx : Fin 0 → Fin d =>
                iteratedWeakSobolevNorm (d := d) 2 2 (iterClassicalPartial (d := d) 0 idx u) Ω)]
        simp [iterClassicalPartial_zero]
      rw [h_sum, zero_mul, add_zero]
  | succ m ih =>
      obtain ⟨N, hN_ne_top, hN⟩ := ih
      refine ⟨(d : ℝ≥0∞) * N + 1, ?_, fun {u} hu_cd hu_cpt => ?_⟩
      · refine (ENNReal.add_ne_top).mpr ⟨?_, by norm_num⟩
        exact ENNReal.mul_ne_top (by norm_num) hN_ne_top
      rw [show m + 1 + 2 = (m + 2) + 1 from by ring,
        wkpNorm_succ_eq_eLpNorm_add_sum_partial (d := d) (m + 2) 2 Ω u]
      have hu_W1 : DeGiorgi.MemW1p (d := d) 2 u Ω :=
        (memWkp_of_smooth_compactSupport_anyOpen (d := d) hΩ hu_cd hu_cpt
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) 1).memW1p
      have h_partial_cd : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
          (fun x : EE => (fderiv ℝ u x) (EuclideanSpace.single i 1)) := by
        intro i
        have h_fderiv : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
          hu_cd.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
        exact (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single i (1 : ℝ))).contDiff.comp h_fderiv
      have h_partial_cpt : ∀ i : Fin d, HasCompactSupport
          (fun x : EE => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
        fun i => hu_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
      have h_chosen_norm : ∀ i : Fin d,
          iteratedWeakSobolevNorm (d := d) (m + 2) 2
              (chosenWeakPartial' (d := d) 2 i u Ω) Ω =
            iteratedWeakSobolevNorm (d := d) (m + 2) 2
              (fun x : EE => (fderiv ℝ u x) (EuclideanSpace.single i 1)) Ω := by
        intro i
        exact wkpNorm_congr_ae (d := d) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ
          (chosenWeakPartial_smooth_ae_eq (d := d)
            (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ hu_cd hu_W1 i)
      have h_ih_partial : ∀ i : Fin d,
          iteratedWeakSobolevNorm (d := d) (m + 2) 2
              (fun x : EE => (fderiv ℝ u x) (EuclideanSpace.single i 1)) Ω ≤
            (∑ idx : Fin m → Fin d,
              iteratedWeakSobolevNorm (d := d) 2 2
                (iterClassicalPartial (d := d) m idx
                  (fun x : EE => (fderiv ℝ u x)
                    (EuclideanSpace.single i 1))) Ω) +
            N * iteratedWeakSobolevNorm (d := d) (m + 1) 2
              (fun x : EE => (fderiv ℝ u x) (EuclideanSpace.single i 1)) Ω :=
        fun i => hN (h_partial_cd i) (h_partial_cpt i)
      have h_iter_cons : ∀ (i : Fin d) (idx : Fin m → Fin d),
          iterClassicalPartial (d := d) m idx
              (fun x : EE => (fderiv ℝ u x) (EuclideanSpace.single i 1)) =
            iterClassicalPartial (d := d) (m + 1)
              (Fin.cons i idx : Fin (m + 1) → Fin d) u := by
        intro i idx
        rw [iterClassicalPartial_succ]
        have h_tail : (fun k : Fin m =>
            (Fin.cons i idx : Fin (m + 1) → Fin d) k.succ) = idx := by
          funext k; simp [Fin.cons_succ]
        have h_head : (Fin.cons i idx : Fin (m + 1) → Fin d) 0 = i := by
          simp [Fin.cons_zero]
        rw [h_tail, h_head]
      have h_partial_le : ∀ i : Fin d,
          iteratedWeakSobolevNorm (d := d) (m + 1) 2
              (fun x : EE => (fderiv ℝ u x) (EuclideanSpace.single i 1)) Ω ≤
            iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω :=
        fun i => wkpNorm_classicalPartial_le (d := d) hΩ hu_cd
          (memWkp_of_smooth_compactSupport_anyOpen (d := d) hΩ hu_cd hu_cpt
            (by norm_num : (1 : ℝ≥0∞) ≤ 2) (m + 2)) i
      have h_reindex :
          ∑ β : Fin (m + 1) → Fin d,
              iteratedWeakSobolevNorm (d := d) 2 2 (iterClassicalPartial (d := d) (m + 1) β u) Ω =
            ∑ i : Fin d, ∑ idx : Fin m → Fin d,
              iteratedWeakSobolevNorm (d := d) 2 2
                (iterClassicalPartial (d := d) m idx
                  (fun x : EE => (fderiv ℝ u x)
                    (EuclideanSpace.single i 1))) Ω := by
        rw [← Fintype.sum_equiv
              (Fin.consEquiv (fun _ : Fin (m + 1) => Fin d))
              (fun (pr : Fin d × (Fin m → Fin d)) =>
                iteratedWeakSobolevNorm (d := d) 2 2 (iterClassicalPartial (d := d) (m + 1)
                  (Fin.cons pr.1 pr.2 : Fin (m + 1) → Fin d) u) Ω)
              (fun β : Fin (m + 1) → Fin d =>
                iteratedWeakSobolevNorm (d := d) 2 2 (iterClassicalPartial (d := d) (m + 1) β u) Ω)
              (fun pr => by simp [Fin.consEquiv])]
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
          (fun idx _ => ?_))
        rw [h_iter_cons i idx]
      have h_eLpNorm_u : eLpNorm u 2 (volume.restrict Ω) ≤
          iteratedWeakSobolevNorm (d := d) (m + 1) 2 u Ω := by
        rw [← wkpNorm_zero (d := d) 2 u Ω]
        exact wkpNorm_mono_order (d := d) (by omega) u Ω
      have h_main :
          eLpNorm u 2 (volume.restrict Ω) +
            ∑ i : Fin d, iteratedWeakSobolevNorm (d := d) (m + 2) 2
              (chosenWeakPartial' (d := d) 2 i u Ω) Ω ≤
            (∑ β : Fin (m + 1) → Fin d,
              iteratedWeakSobolevNorm (d := d) 2 2
                (iterClassicalPartial (d := d) (m + 1) β u) Ω) +
            ((d : ℝ≥0∞) * N + 1) * iteratedWeakSobolevNorm (d := d) (m + 1 + 1) 2 u Ω := by
        have h_sum_eq :
            ∑ i : Fin d, iteratedWeakSobolevNorm (d := d) (m + 2) 2
                (chosenWeakPartial' (d := d) 2 i u Ω) Ω =
              ∑ i : Fin d, iteratedWeakSobolevNorm (d := d) (m + 2) 2
                (fun x : EE => (fderiv ℝ u x)
                  (EuclideanSpace.single i 1)) Ω :=
          Finset.sum_congr rfl (fun i _ => h_chosen_norm i)
        rw [h_sum_eq]
        have h_step1 :
            ∑ i : Fin d, iteratedWeakSobolevNorm (d := d) (m + 2) 2
                (fun x : EE => (fderiv ℝ u x)
                  (EuclideanSpace.single i 1)) Ω ≤
              ∑ i : Fin d,
                ((∑ idx : Fin m → Fin d,
                  iteratedWeakSobolevNorm (d := d) 2 2
                    (iterClassicalPartial (d := d) m idx
                      (fun x : EE => (fderiv ℝ u x)
                        (EuclideanSpace.single i 1))) Ω) +
                N * iteratedWeakSobolevNorm (d := d) (m + 1) 2
                  (fun x : EE => (fderiv ℝ u x)
                    (EuclideanSpace.single i 1)) Ω) :=
          Finset.sum_le_sum (fun i _ => h_ih_partial i)
        rw [Finset.sum_add_distrib] at h_step1
        rw [← h_reindex] at h_step1
        have h_lower :
            ∑ i : Fin d, N * iteratedWeakSobolevNorm (d := d) (m + 1) 2
                (fun x : EE => (fderiv ℝ u x)
                  (EuclideanSpace.single i 1)) Ω ≤
              (d : ℝ≥0∞) * N * iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω := by
          calc ∑ i : Fin d, N * iteratedWeakSobolevNorm (d := d) (m + 1) 2
                  (fun x : EE => (fderiv ℝ u x)
                    (EuclideanSpace.single i 1)) Ω
              ≤ ∑ _i : Fin d, N * iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω :=
                Finset.sum_le_sum (fun i _ =>
                  mul_le_mul_of_nonneg_left (h_partial_le i) (zero_le _))
            _ = (d : ℝ≥0∞) * (N * iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                  nsmul_eq_mul]
            _ = (d : ℝ≥0∞) * N * iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω := by ring
        calc eLpNorm u 2 (volume.restrict Ω) +
              ∑ i : Fin d, iteratedWeakSobolevNorm (d := d) (m + 2) 2
                (fun x : EE => (fderiv ℝ u x)
                  (EuclideanSpace.single i 1)) Ω
            ≤ iteratedWeakSobolevNorm (d := d) (m + 1) 2 u Ω +
                ((∑ β : Fin (m + 1) → Fin d,
                  iteratedWeakSobolevNorm (d := d) 2 2
                    (iterClassicalPartial (d := d) (m + 1) β u) Ω) +
                (d : ℝ≥0∞) * N * iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω) :=
              add_le_add h_eLpNorm_u (h_step1.trans (add_le_add le_rfl h_lower))
          _ = (∑ β : Fin (m + 1) → Fin d,
                iteratedWeakSobolevNorm (d := d) 2 2
                  (iterClassicalPartial (d := d) (m + 1) β u) Ω) +
              ((d : ℝ≥0∞) * N * iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω +
                iteratedWeakSobolevNorm (d := d) (m + 1) 2 u Ω) := by ring
          _ ≤ (∑ β : Fin (m + 1) → Fin d,
                iteratedWeakSobolevNorm (d := d) 2 2
                  (iterClassicalPartial (d := d) (m + 1) β u) Ω) +
              ((d : ℝ≥0∞) * N + 1) * iteratedWeakSobolevNorm (d := d) (m + 1 + 1) 2 u Ω := by
              refine add_le_add le_rfl ?_
              rw [add_mul, one_mul]
              refine add_le_add (le_of_eq ?_)
                (wkpNorm_mono_order (d := d) (by omega) u Ω)
              norm_num
      exact h_main

omit [NeZero d] in

private theorem tsupport_finsetSum_subset_of_forall
    {ι : Type*} (S : Finset ι) (F : ι → EE → ℝ) {B : Set EE}
    (hB_closed : IsClosed B) (hF : ∀ a ∈ S, tsupport (F a) ⊆ B) :
    tsupport (fun x => ∑ a ∈ S, F a x) ⊆ B := by
  classical
  refine closure_minimal ?_ hB_closed
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxB
  exact hx (Finset.sum_eq_zero (fun a ha => by
    have hax : x ∉ tsupport (F a) := fun h => hxB (hF a ha h)
    exact image_eq_zero_of_notMem_tsupport hax))

private theorem tsupport_perturbedSource_subset
    (B : SmoothEllipticBilinearForm d (Set.univ : Set EE))
    {u f : EE → ℝ} {S : Set EE} (hS_closed : IsClosed S)
    (hu_S : tsupport u ⊆ S) (hf_S : tsupport f ⊆ S) (l : Fin d) :
    tsupport (perturbedSource (d := d) B u f l) ⊆ S := by
  classical
  set termA : EE → ℝ :=
    fun x => (fderiv ℝ f x) (EuclideanSpace.single l 1) with hA_def
  set termB : EE → ℝ :=
    fun x => (fderiv ℝ B.c x) (EuclideanSpace.single l 1) * u x with hB_def
  set termC : EE → ℝ :=
    fun x => ∑ i : Fin d, ∑ j : Fin d, (fderiv ℝ (fun y : EE =>
      (fderiv ℝ (fun z : EE => B.a z i j) y) (EuclideanSpace.single l 1) *
        (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
      (EuclideanSpace.single j 1) with hC_def
  have h_dlf : tsupport termA ⊆ S := by
    rw [hA_def]
    exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single l 1)).trans hf_S
  have h_dlc_u : tsupport termB ⊆ S := by
    rw [hB_def]
    exact (tsupport_mul_subset_right
      (f := fun x : EE => (fderiv ℝ B.c x) (EuclideanSpace.single l 1))
      (g := u)).trans hu_S
  have h_div_summand : ∀ i j : Fin d, tsupport
      (fun x : EE => (fderiv ℝ (fun y : EE =>
        (fderiv ℝ (fun z : EE => B.a z i j) y) (EuclideanSpace.single l 1) *
          (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
        (EuclideanSpace.single j 1)) ⊆ S := by
    intro i j
    refine (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single j 1)).trans ?_
    refine (tsupport_mul_subset_right
      (f := fun y : EE =>
        (fderiv ℝ (fun z : EE => B.a z i j) y) (EuclideanSpace.single l 1))
      (g := fun y : EE => (fderiv ℝ u y) (EuclideanSpace.single i 1))).trans ?_
    exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans hu_S
  have h_row : ∀ i : Fin d, tsupport
      (fun x : EE => ∑ j : Fin d, (fderiv ℝ (fun y : EE =>
        (fderiv ℝ (fun z : EE => B.a z i j) y) (EuclideanSpace.single l 1) *
          (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)
        (EuclideanSpace.single j 1)) ⊆ S :=
    fun i => tsupport_finsetSum_subset_of_forall Finset.univ _ hS_closed
      (fun j _ => h_div_summand i j)
  have h_div : tsupport termC ⊆ S := by
    rw [hC_def]
    exact tsupport_finsetSum_subset_of_forall Finset.univ _ hS_closed
      (fun i _ => h_row i)
  have h_pert_eq : perturbedSource (d := d) B u f l =
      (fun x => (termA x - termB x) + termC x) := by
    funext x; rw [hA_def, hB_def, hC_def]; unfold perturbedSource; rfl
  rw [h_pert_eq]
  refine closure_minimal ?_ hS_closed
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxS
  apply hx
  have hx1 : termA x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hxS (h_dlf h))
  have hx2 : termB x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hxS (h_dlc_u h))
  have hx3 : termC x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hxS (h_div h))
  rw [hx1, hx2, hx3]; ring

theorem tsupport_iteratedPerturbedSource_subset
    (B : SmoothEllipticBilinearForm d (Set.univ : Set EE)) (m : ℕ) :
    ∀ {u f : EE → ℝ} {S : Set EE}, IsClosed S →
      tsupport u ⊆ S → tsupport f ⊆ S → ∀ idx : Fin m → Fin d,
        tsupport (iteratedPerturbedSource (d := d) B m u f idx) ⊆ S := by
  induction m with
  | zero =>
      intro u f S _hS_closed _hu_S hf_S idx
      rw [iteratedPerturbedSource_zero]
      exact hf_S
  | succ m ih =>
      intro u f S hS_closed hu_S hf_S idx
      rw [iteratedPerturbedSource_succ]
      have h_du_S : tsupport
          (fun x : EE => (fderiv ℝ u x)
            (EuclideanSpace.single (idx 0) 1)) ⊆ S :=
        (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single (idx 0) 1)).trans
          hu_S
      have h_ps_S : tsupport (perturbedSource (d := d) B u f (idx 0)) ⊆ S :=
        tsupport_perturbedSource_subset (d := d) B hS_closed hu_S hf_S (idx 0)
      exact ih hS_closed h_du_S h_ps_S (fun i : Fin m => idx i.succ)

theorem contDiff_iteratedPerturbedSource
    (B : SmoothEllipticBilinearForm d (Set.univ : Set EE)) (m : ℕ) :
    ∀ {u f : EE → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u → ContDiff ℝ (⊤ : ℕ∞) f →
      ∀ idx : Fin m → Fin d,
        ContDiff ℝ (⊤ : ℕ∞) (iteratedPerturbedSource (d := d) B m u f idx) := by
  induction m with
  | zero =>
      intro u f _hu hf idx
      rw [iteratedPerturbedSource_zero]
      exact hf
  | succ m ih =>
      intro u f hu hf idx
      rw [iteratedPerturbedSource_succ]
      have h_du : ContDiff ℝ (⊤ : ℕ∞)
          (fun x : EE => (fderiv ℝ u x)
            (EuclideanSpace.single (idx 0) 1)) := by
        have h_fderiv : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
          hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
        exact (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single (idx 0) (1 : ℝ))).contDiff.comp h_fderiv
      exact ih h_du (contDiff_perturbedSource' (d := d) B hu hf (idx 0))
        (fun i : Fin m => idx i.succ)

private theorem wkpNorm_iteratedPerturbedSource_zero_le
    (B : SmoothEllipticBilinearForm d (Set.univ : Set EE)) (m : ℕ)
    {Ω : Set EE} (hΩ_open : IsOpen Ω)
    (hΩ_compact_closure : IsCompact (closure Ω)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : EE → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∀ idx : Fin m → Fin d,
        iteratedWeakSobolevNorm (d := d) 0 2
            (iteratedPerturbedSource (d := d) B m u f idx) Ω ≤
          ENNReal.ofReal C *
            (iteratedWeakSobolevNorm (d := d) m 2 f Ω + iteratedWeakSobolevNorm (d := d) (m + 1) 2 u Ω) := by
  classical
  induction m with
  | zero =>
      refine ⟨1, by norm_num, fun {u f} _hu_cd _hu_cpt _hf_cd _hf_cpt idx => ?_⟩
      rw [iteratedPerturbedSource_zero, ENNReal.ofReal_one, one_mul]
      exact le_self_add
  | succ m ih =>
      obtain ⟨C, hC_nn, hC⟩ := ih
      have h_step_data : ∀ l : Fin d, ∃ K : ℝ, 0 ≤ K ∧ ∀ {u f : EE → ℝ},
          ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
          ContDiff ℝ (⊤ : ℕ∞) f →
          MemWkp (d := d) (m + 2) 2 u Ω → MemWkp (d := d) (m + 1) 2 f Ω →
          MemWkp (d := d) m 2 (perturbedSource (d := d) B u f l) Ω ∧
            iteratedWeakSobolevNorm (d := d) m 2 (perturbedSource (d := d) B u f l) Ω ≤
              ENNReal.ofReal K *
                (iteratedWeakSobolevNorm (d := d) (m + 1) 2 f Ω +
                  iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω) := fun l =>
        perturbedSource_memWkp_of_source_memWkp (d := d) B m hΩ_open
          hΩ_compact_closure l
      choose K_step hK_step_nn hK_step_bound using h_step_data
      set Kmax : ℝ := (Finset.univ : Finset (Fin d)).sup'
        (Finset.univ_nonempty) K_step with hKmax_def
      have hKmax_nn : 0 ≤ Kmax := by
        rw [hKmax_def]
        exact le_trans (hK_step_nn (Classical.arbitrary (Fin d)))
          (Finset.le_sup' K_step (Finset.mem_univ _))
      have hK_step_le_Kmax : ∀ l : Fin d, K_step l ≤ Kmax :=
        fun l => Finset.le_sup' K_step (Finset.mem_univ l)
      refine ⟨C * (Kmax + 1), by positivity,
        fun {u f} hu_cd hu_cpt hf_cd hf_cpt idx => ?_⟩
      rw [iteratedPerturbedSource_succ]
      set u' : EE → ℝ :=
        fun x => (fderiv ℝ u x) (EuclideanSpace.single (idx 0) 1) with hu'_def
      have hu'_cd : ContDiff ℝ (⊤ : ℕ∞) u' := by
        have h_fderiv : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
          hu_cd.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
        exact (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single (idx 0) (1 : ℝ))).contDiff.comp h_fderiv
      have hu'_cpt : HasCompactSupport u' :=
        hu_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single (idx 0) 1)
      set f' : EE → ℝ := perturbedSource (d := d) B u f (idx 0) with hf'_def
      have hf'_cd : ContDiff ℝ (⊤ : ℕ∞) f' :=
        contDiff_perturbedSource' (d := d) B hu_cd hf_cd (idx 0)
      have hf'_cpt : HasCompactSupport f' := by
        rw [hf'_def]
        refine HasCompactSupport.of_support_subset_isCompact
          (hu_cpt.union hf_cpt) ?_
        refine subset_trans (subset_tsupport _) ?_
        exact tsupport_perturbedSource_subset (d := d) B
          (isClosed_tsupport u |>.union (isClosed_tsupport f))
          (subset_union_left) (subset_union_right) (idx 0)
      have h_ih := hC hu'_cd hu'_cpt hf'_cd hf'_cpt (fun i : Fin m => idx i.succ)
      have hu_mem_succ2 : MemWkp (d := d) (m + 2) 2 u Ω :=
        memWkp_of_smooth_compactSupport_anyOpen (d := d) hΩ_open hu_cd hu_cpt
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) (m + 2)
      have hf_mem_succ : MemWkp (d := d) (m + 1) 2 f Ω :=
        memWkp_of_smooth_compactSupport_anyOpen (d := d) hΩ_open hf_cd hf_cpt
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) (m + 1)
      have hf'_norm :=
        (hK_step_bound (idx 0) hu_cd hu_cpt hf_cd hu_mem_succ2 hf_mem_succ).2
      have hf'_le :
          iteratedWeakSobolevNorm (d := d) m 2 f' Ω ≤
            ENNReal.ofReal Kmax *
              (iteratedWeakSobolevNorm (d := d) (m + 1) 2 f Ω +
                iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω) := by
        refine hf'_norm.trans ?_
        exact mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal (hK_step_le_Kmax (idx 0))) (zero_le _)
      have hu'_le : iteratedWeakSobolevNorm (d := d) (m + 1) 2 u' Ω ≤
          iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω :=
        wkpNorm_classicalPartial_le (d := d) hΩ_open hu_cd hu_mem_succ2 (idx 0)
      refine h_ih.trans ?_
      rw [ENNReal.ofReal_mul hC_nn, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
      calc iteratedWeakSobolevNorm (d := d) m 2 f' Ω + iteratedWeakSobolevNorm (d := d) (m + 1) 2 u' Ω
          ≤ (ENNReal.ofReal Kmax *
              (iteratedWeakSobolevNorm (d := d) (m + 1) 2 f Ω +
                iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω)) +
              iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω :=
            add_le_add hf'_le hu'_le
        _ ≤ ENNReal.ofReal Kmax *
              (iteratedWeakSobolevNorm (d := d) (m + 1) 2 f Ω +
                iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω) +
              (1 : ℝ≥0∞) * (iteratedWeakSobolevNorm (d := d) (m + 1) 2 f Ω +
                iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω) := by
            refine add_le_add le_rfl ?_
            rw [one_mul]
            exact le_add_self
        _ = (ENNReal.ofReal Kmax + 1) *
              (iteratedWeakSobolevNorm (d := d) (m + 1) 2 f Ω +
                iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω) := by rw [add_mul]
        _ = ENNReal.ofReal (Kmax + 1) *
              (iteratedWeakSobolevNorm (d := d) (m + 1) 2 f Ω +
                iteratedWeakSobolevNorm (d := d) (m + 2) 2 u Ω) := by
            rw [ENNReal.ofReal_add hKmax_nn (by norm_num : (0 : ℝ) ≤ 1),
              ENNReal.ofReal_one]

omit [NeZero d] in
theorem tsupport_iterClassicalPartial_subset (m : ℕ) :
    ∀ (idx : Fin m → Fin d) {h : EE → ℝ} {S : Set EE}, IsClosed S →
      tsupport h ⊆ S → tsupport (iterClassicalPartial (d := d) m idx h) ⊆ S := by
  induction m with
  | zero =>
      intro idx h S _hS_closed hh_S
      rw [iterClassicalPartial_zero]
      exact hh_S
  | succ m ih =>
      intro idx h S hS_closed hh_S
      rw [iterClassicalPartial_succ]
      refine ih (fun i : Fin m => idx i.succ) hS_closed ?_
      exact (tsupport_fderiv_apply_subset ℝ
        (EuclideanSpace.single (idx 0) 1)).trans hh_S

omit [NeZero d] in
private theorem wkpNorm_iterClassicalPartial_le
    {Ω : Set EE} (hΩ : IsOpen Ω) (k : ℕ) :
    ∀ (m : ℕ) (idx : Fin m → Fin d) {u : EE → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
      iteratedWeakSobolevNorm (d := d) k 2 (iterClassicalPartial (d := d) m idx u) Ω ≤
        iteratedWeakSobolevNorm (d := d) (m + k) 2 u Ω := by
  intro m
  induction m with
  | zero =>
      intro idx u _hu_cd _hu_cpt
      rw [iterClassicalPartial_zero]
      exact le_of_eq (by rw [Nat.zero_add])
  | succ m ih =>
      intro idx u hu_cd hu_cpt
      rw [iterClassicalPartial_succ]
      set u' : EE → ℝ :=
        fun x => (fderiv ℝ u x) (EuclideanSpace.single (idx 0) 1) with hu'_def
      have hu'_cd : ContDiff ℝ (⊤ : ℕ∞) u' := by
        have h_fderiv : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
          hu_cd.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
        exact (ContinuousLinearMap.apply ℝ ℝ
          (EuclideanSpace.single (idx 0) (1 : ℝ))).contDiff.comp h_fderiv
      have hu'_cpt : HasCompactSupport u' :=
        hu_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single (idx 0) 1)
      refine (ih (fun i : Fin m => idx i.succ) hu'_cd hu'_cpt).trans ?_
      have h_drop : iteratedWeakSobolevNorm (d := d) (m + k) 2 u' Ω ≤
          iteratedWeakSobolevNorm (d := d) (m + k + 1) 2 u Ω :=
        wkpNorm_classicalPartial_le (d := d) hΩ hu_cd
          (memWkp_of_smooth_compactSupport_anyOpen (d := d) hΩ hu_cd hu_cpt
            (by norm_num : (1 : ℝ≥0∞) ≤ 2) (m + k + 1)) (idx 0)
      refine h_drop.trans (le_of_eq ?_)
      congr 1
      omega

omit [NeZero d] in

private lemma rpow_half_add_le {a b : ℝ≥0∞} :
    (a + b) ^ ((1 : ℝ) / 2) ≤ a ^ ((1 : ℝ) / 2) + b ^ ((1 : ℝ) / 2) :=
  ENNReal.rpow_add_le_add_rpow a b (by norm_num) (by norm_num)

omit [NeZero d] in

private lemma rpow_half_sq_add_sq_le {a b : ℝ≥0∞} :
    (a ^ 2 + b ^ 2) ^ ((1 : ℝ) / 2) ≤ a + b := by
  have h_le : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by
    rw [add_sq]
    exact add_le_add le_self_add le_rfl
  calc (a ^ 2 + b ^ 2) ^ ((1 : ℝ) / 2)
      ≤ ((a + b) ^ 2) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow h_le (by norm_num)
    _ = a + b := by
        rw [← ENNReal.rpow_natCast (a + b) 2, ← ENNReal.rpow_mul]
        norm_num

omit [NeZero d] in

private lemma eLpNorm_two_sq_eq_ofReal_integral_sq_univ
    {Ω : Set EE} {h : EE → ℝ}
    (hh_cd : ContDiff ℝ (⊤ : ℕ∞) h) (hh_cpt : HasCompactSupport h)
    (hh_S : tsupport h ⊆ Ω) :
    (eLpNorm h 2 (volume.restrict Ω)) ^ 2 =
      ENNReal.ofReal (∫ x, h x ^ 2 ∂(volume : Measure EE)) := by
  classical
  have hh_l2 : MemLp h 2 (volume.restrict Ω) :=
    (hh_cd.continuous.memLp_of_hasCompactSupport
      (μ := (volume : Measure EE)) (p := 2) hh_cpt).restrict _
  have h_sq : (eLpNorm h 2 (volume.restrict Ω)) ^ 2 =
      ENNReal.ofReal (∫ x in Ω, h x ^ 2 ∂(volume : Measure EE)) := by
    have h_sq_lintegral :
        (eLpNorm h 2 (volume.restrict Ω)) ^ 2 =
          ∫⁻ x, (‖h x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume.restrict Ω) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))]
      have h2 : (2 : ℝ≥0∞).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
      rw [h2]
      have h_inner_eq : ∫⁻ x, (‖h x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂(volume.restrict Ω) =
          ∫⁻ x, (‖h x‖ₑ : ℝ≥0∞) ^ 2 ∂(volume.restrict Ω) := by
        refine lintegral_congr_ae ?_
        filter_upwards with x
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
      rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
      norm_num
    rw [h_sq_lintegral]
    have h_pt : ∀ x : EE, (‖h x‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (h x ^ 2) := by
      intro x
      rw [← Real.enorm_eq_ofReal (sq_nonneg _),
        show h x ^ 2 = h x * h x from by ring, enorm_mul,
        show (‖h x‖ₑ : ℝ≥0∞) ^ 2 = ‖h x‖ₑ * ‖h x‖ₑ from by ring]
    rw [lintegral_congr (fun x => h_pt x)]
    have h_sq_int : Integrable (fun x => h x ^ 2) (volume.restrict Ω) := by
      have := hh_l2.integrable_sq
      simpa [pow_two] using this
    exact (ofReal_integral_eq_lintegral_ofReal h_sq_int
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))).symm
  rw [h_sq]
  congr 1
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
  have hx_supp : x ∉ tsupport h := fun h' => hx (hh_S h')
  rw [image_eq_zero_of_notMem_tsupport hx_supp]; ring

private theorem smooth_cc_wkp2_wkpNorm_le
    (B : SmoothEllipticBilinearForm d (Set.univ : Set EE))
    {Ω'' : Set EE} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω'')) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {w s : EE → ℝ}, B.IsSmoothWeakSolution w s →
      HasCompactSupport w → ContDiff ℝ (⊤ : ℕ∞) s → HasCompactSupport s →
      tsupport w ⊆ Ω'' → tsupport s ⊆ Ω'' →
      iteratedWeakSobolevNorm (d := d) 2 2 w Ω'' ≤
        ENNReal.ofReal C *
          (iteratedWeakSobolevNorm (d := d) 1 2 w Ω'' + iteratedWeakSobolevNorm (d := d) 0 2 s Ω'') := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    smooth_cc_h2_loc_memWkp_two (d := d) B hΩ'' hΩ''_compact_closure
  refine ⟨C, hC_nn, fun {w s} h_weak hw_cpt hs_cd hs_cpt hw_S hs_S => ?_⟩
  have hw_cd : ContDiff ℝ (⊤ : ℕ∞) w := h_weak.1
  obtain ⟨_h_memWkp, h_engine_le⟩ := hC h_weak hw_cpt hs_cd hs_cpt
  have hw_partial_cd : ∀ j : Fin d, ContDiff ℝ (⊤ : ℕ∞)
      (fun x : EE => (fderiv ℝ w x) (EuclideanSpace.single j 1)) := by
    intro j
    have h_fderiv : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ w) :=
      hw_cd.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    exact (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single j (1 : ℝ))).contDiff.comp h_fderiv
  have hw_partial_cpt : ∀ j : Fin d, HasCompactSupport
      (fun x : EE => (fderiv ℝ w x) (EuclideanSpace.single j 1)) :=
    fun j => hw_cpt.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)
  have hw_partial_S : ∀ j : Fin d, tsupport
      (fun x : EE => (fderiv ℝ w x) (EuclideanSpace.single j 1)) ⊆ Ω'' :=
    fun j => (tsupport_fderiv_apply_subset ℝ
      (EuclideanSpace.single j 1)).trans hw_S
  have hw_W1 : DeGiorgi.MemW1p (d := d) 2 w Ω'' :=
    (memWkp_of_smooth_compactSupport_anyOpen (d := d) hΩ'' hw_cd hw_cpt
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) 1).memW1p
  have hw_eLp_sq : (eLpNorm w 2 (volume.restrict Ω'')) ^ 2 =
      ENNReal.ofReal (∫ x, w x ^ 2 ∂(volume : Measure EE)) :=
    eLpNorm_two_sq_eq_ofReal_integral_sq_univ (d := d) hw_cd hw_cpt hw_S
  have hw_partial_eLp_sq : ∀ j : Fin d,
      (eLpNorm (chosenWeakPartial' (d := d) 2 j w Ω'') 2
          (volume.restrict Ω'')) ^ 2 =
        ENNReal.ofReal (∫ x,
          ((fderiv ℝ w x) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure EE)) := by
    intro j
    rw [eLpNorm_congr_ae (chosenWeakPartial_smooth_ae_eq (d := d)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ'' hw_cd hw_W1 j)]
    exact eLpNorm_two_sq_eq_ofReal_integral_sq_univ (d := d)
      (hw_partial_cd j) (hw_partial_cpt j) (hw_partial_S j)
  have hs_eLp_sq : (eLpNorm s 2 (volume.restrict Ω'')) ^ 2 =
      ENNReal.ofReal (∫ x, s x ^ 2 ∂(volume : Measure EE)) :=
    eLpNorm_two_sq_eq_ofReal_integral_sq_univ (d := d) hs_cd hs_cpt hs_S
  set D : ℝ :=
    (∫ x, ∑ j : Fin d, ((fderiv ℝ w x) (EuclideanSpace.single j 1)) ^ 2
      ∂(volume : Measure EE)) +
    (∫ x, (w x) ^ 2 ∂(volume : Measure EE)) +
    (∫ x, (s x) ^ 2 ∂(volume : Measure EE)) with hD_def
  have hD_nn : 0 ≤ D := by
    have h1 : 0 ≤ ∫ x, ∑ j : Fin d,
        ((fderiv ℝ w x) (EuclideanSpace.single j 1)) ^ 2 ∂(volume : Measure EE) :=
      integral_nonneg (fun x => Finset.sum_nonneg (fun j _ => sq_nonneg _))
    have h2 : 0 ≤ ∫ x, (w x) ^ 2 ∂(volume : Measure EE) :=
      integral_nonneg (fun x => sq_nonneg _)
    have h3 : 0 ≤ ∫ x, (s x) ^ 2 ∂(volume : Measure EE) :=
      integral_nonneg (fun x => sq_nonneg _)
    rw [hD_def]; positivity
  have hw_W1_sq : ENNReal.ofReal
      ((∫ x, ∑ j : Fin d,
          ((fderiv ℝ w x) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure EE)) +
        (∫ x, (w x) ^ 2 ∂(volume : Measure EE))) ≤
      (iteratedWeakSobolevNorm (d := d) 1 2 w Ω'') ^ 2 := by
    have h_int_swap :
        (∫ x, ∑ j : Fin d,
          ((fderiv ℝ w x) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure EE)) =
        ∑ j : Fin d, ∫ x,
          ((fderiv ℝ w x) (EuclideanSpace.single j 1)) ^ 2
          ∂(volume : Measure EE) := by
      rw [integral_finset_sum]
      intro j _
      exact (((hw_partial_cd j).continuous).pow 2).integrable_of_hasCompactSupport
        (hasCompactSupport_sq (d := d) (hw_partial_cpt j))
    rw [h_int_swap]
    have h_ofReal_eq : ENNReal.ofReal
        ((∑ j : Fin d, ∫ x,
            ((fderiv ℝ w x) (EuclideanSpace.single j 1)) ^ 2
            ∂(volume : Measure EE)) +
          (∫ x, (w x) ^ 2 ∂(volume : Measure EE))) =
        (∑ j : Fin d, (eLpNorm (chosenWeakPartial' (d := d) 2 j w Ω'') 2
            (volume.restrict Ω'')) ^ 2) +
          (eLpNorm w 2 (volume.restrict Ω'')) ^ 2 := by
      rw [ENNReal.ofReal_add
          (Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _)))
          (integral_nonneg (fun x => sq_nonneg _)),
        ENNReal.ofReal_sum_of_nonneg
          (fun j _ => integral_nonneg (fun x => sq_nonneg _)),
        hw_eLp_sq]
      refine congrArg (· + _) (Finset.sum_congr rfl (fun j _ => ?_))
      rw [hw_partial_eLp_sq j]
    rw [h_ofReal_eq]
    have h_wkp1 : iteratedWeakSobolevNorm (d := d) 1 2 w Ω'' =
        eLpNorm w 2 (volume.restrict Ω'') +
          ∑ j : Fin d, eLpNorm (chosenWeakPartial' (d := d) 2 j w Ω'') 2
            (volume.restrict Ω'') := by
      rw [wkpNorm_succ_eq_eLpNorm_add_sum_partial (d := d) 0 2 Ω'' w]
      refine congrArg (_ + ·) (Finset.sum_congr rfl (fun j _ => ?_))
      rw [wkpNorm_zero]
    rw [h_wkp1]
    set b : ℝ≥0∞ := eLpNorm w 2 (volume.restrict Ω'') with hb_def
    set aj : Fin d → ℝ≥0∞ :=
      fun j => eLpNorm (chosenWeakPartial' (d := d) 2 j w Ω'') 2
        (volume.restrict Ω'') with haj_def
    have h_sumsq_le : (∑ j : Fin d, (aj j) ^ 2) ≤ (∑ j : Fin d, aj j) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => zero_le _)
    calc (∑ j : Fin d, (aj j) ^ 2) + b ^ 2
        ≤ (∑ j : Fin d, aj j) ^ 2 + b ^ 2 :=
          add_le_add h_sumsq_le le_rfl
      _ = b ^ 2 + (∑ j : Fin d, aj j) ^ 2 := by rw [add_comm]
      _ ≤ (b + ∑ j : Fin d, aj j) ^ 2 := by
          rw [add_sq]
          exact add_le_add le_self_add le_rfl
  have hs_wkp0_sq : ENNReal.ofReal (∫ x, (s x) ^ 2 ∂(volume : Measure EE)) =
      (iteratedWeakSobolevNorm (d := d) 0 2 s Ω'') ^ 2 := by
    rw [wkpNorm_zero, ← hs_eLp_sq]
  refine h_engine_le.trans ?_
  rw [ENNReal.ofReal_mul hC_nn,
    (rpow_half_ofReal_eq_ofReal_sqrt hD_nn).symm]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  have hD_split : ENNReal.ofReal D =
      ENNReal.ofReal
        ((∫ x, ∑ j : Fin d,
            ((fderiv ℝ w x) (EuclideanSpace.single j 1)) ^ 2
            ∂(volume : Measure EE)) +
          (∫ x, (w x) ^ 2 ∂(volume : Measure EE))) +
        ENNReal.ofReal (∫ x, (s x) ^ 2 ∂(volume : Measure EE)) := by
    rw [hD_def, ← ENNReal.ofReal_add
      (by positivity) (integral_nonneg (fun x => sq_nonneg _))]
  rw [hD_split]
  calc (ENNReal.ofReal
        ((∫ x, ∑ j : Fin d,
            ((fderiv ℝ w x) (EuclideanSpace.single j 1)) ^ 2
            ∂(volume : Measure EE)) +
          (∫ x, (w x) ^ 2 ∂(volume : Measure EE))) +
        ENNReal.ofReal (∫ x, (s x) ^ 2 ∂(volume : Measure EE))) ^
          ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal
          ((∫ x, ∑ j : Fin d,
              ((fderiv ℝ w x) (EuclideanSpace.single j 1)) ^ 2
              ∂(volume : Measure EE)) +
            (∫ x, (w x) ^ 2 ∂(volume : Measure EE)))) ^ ((1 : ℝ) / 2) +
        (ENNReal.ofReal (∫ x, (s x) ^ 2 ∂(volume : Measure EE))) ^
          ((1 : ℝ) / 2) := rpow_half_add_le
    _ ≤ ((iteratedWeakSobolevNorm (d := d) 1 2 w Ω'') ^ 2) ^ ((1 : ℝ) / 2) +
        ((iteratedWeakSobolevNorm (d := d) 0 2 s Ω'') ^ 2) ^ ((1 : ℝ) / 2) := by
        refine add_le_add (ENNReal.rpow_le_rpow hw_W1_sq (by norm_num)) ?_
        rw [hs_wkp0_sq]
    _ = iteratedWeakSobolevNorm (d := d) 1 2 w Ω'' + iteratedWeakSobolevNorm (d := d) 0 2 s Ω'' := by
        rw [← ENNReal.rpow_natCast (iteratedWeakSobolevNorm (d := d) 1 2 w Ω'') 2,
          ← ENNReal.rpow_mul,
          ← ENNReal.rpow_natCast (iteratedWeakSobolevNorm (d := d) 0 2 s Ω'') 2,
          ← ENNReal.rpow_mul]
        norm_num

end GenericEuclidean

section TensorAPriori

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

local notation "dimE" => Module.finrank ℝ E

set_option maxHeartbeats 1600000 in

private theorem tensorComponent_aPriori_succ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (m : ℕ) (P₀ : CompIdx E r s)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hK_Ω'' : K ⊆ Ω'') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T F : SmoothCcTensor g r s),
      tsupport T.toFun ⊆ (chartAt H α).source →
      tsupport F.toFun ⊆ (chartAt H α).source →
      (∀ P : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
      (∀ Q : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s F α Q) ⊆ K) →
      (∀ v : SmoothCcTensor g r s,
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) →
      iteratedWeakSobolevNorm (d := dimE) (m + 2) 2
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) Ω'' ≤
        ENNReal.ofReal C *
          (iteratedWeakSobolevNorm (d := dimE) m 2
              (tensorComponentWeakRHS (I := I) (M := M)
                g r s T F α hK hK_target P₀) Ω'' +
            iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
              (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) Ω'') := by
  classical
  set B := tensorPrincipalForm (I := I) (M := M) g α hK hK_target with hB_def
  obtain ⟨N, hN_ne_top, hN⟩ := wkpNorm_assembly_le (d := dimE) m hΩ''_open
  have hN_toReal_nn : 0 ≤ N.toReal := ENNReal.toReal_nonneg
  have hN_eq : N = ENNReal.ofReal N.toReal :=
    (ENNReal.ofReal_toReal hN_ne_top).symm
  obtain ⟨Cw, hCw_nn, hCw⟩ :=
    smooth_cc_wkp2_wkpNorm_le (d := dimE) B hΩ''_open hΩ''_compact_closure
  obtain ⟨Cs, hCs_nn, hCs⟩ :=
    wkpNorm_iteratedPerturbedSource_zero_le (d := dimE) B m hΩ''_open
      hΩ''_compact_closure
  refine ⟨((dimE : ℝ) ^ m) * Cw * (Cs + 1) + N.toReal, by positivity, ?_⟩
  intro T F hT_supp hF_supp hT_K hF_K hweak
  set u := tensorComponentEuclid (I := I) (M := M) g r s T α P₀ with hu_def
  set RHS := tensorComponentWeakRHS (I := I) (M := M)
    g r s T F α hK hK_target P₀ with hRHS_def
  have hu_cd : ContDiff ℝ (⊤ : ℕ∞) u :=
    tensorComponentEuclid_contDiff (I := I) (M := M) g r s T α P₀ hT_supp
  have hu_cpt : HasCompactSupport u :=
    tensorComponentEuclid_hasCompactSupport (I := I) (M := M)
      g r s T α P₀ hT_supp
  have hu_K : tsupport u ⊆ K := hT_K P₀
  have hu_Ω'' : tsupport u ⊆ Ω'' := hu_K.trans hK_Ω''
  have hRHS_cd : ContDiff ℝ (⊤ : ℕ∞) RHS :=
    tensorComponentWeakRHS_contDiff (I := I) (M := M)
      g r s T F α hK hK_target P₀ hT_supp hF_supp
  have hRHS_u : tsupport RHS ⊆ tsupport u :=
    tensorComponentWeakRHS_tsupport_subset (I := I) (M := M) g r s T F α hK
      hK_target P₀ hT_supp hF_supp hu_K hweak
  have hRHS_cpt : HasCompactSupport RHS :=
    HasCompactSupport.of_support_subset_isCompact hu_cpt.isCompact
      (fun x hx => hRHS_u (subset_tsupport _ hx))
  have h_assembly := hN hu_cd hu_cpt
  have h_partial_le : ∀ idx : Fin m → Fin dimE,
      iteratedWeakSobolevNorm (d := dimE) 2 2
          (iterClassicalPartial (d := dimE) m idx u) Ω'' ≤
        ENNReal.ofReal Cw *
          ((ENNReal.ofReal Cs + 1) *
            (iteratedWeakSobolevNorm (d := dimE) m 2 RHS Ω'' +
              iteratedWeakSobolevNorm (d := dimE) (m + 1) 2 u Ω'')) := by
    intro idx
    have h_weak_sol :
        B.IsSmoothWeakSolution
          (iterClassicalPartial (d := dimE) m idx u)
          (iteratedPerturbedSource (d := dimE) B m u RHS idx) :=
      tensorComponent_iterated_partial_isSmoothWeakSolution (I := I) (M := M)
        g r s T F α hK hK_target P₀ hT_supp hF_supp hu_K hweak m idx
    have h_w_cpt : HasCompactSupport (iterClassicalPartial (d := dimE) m idx u) :=
      hasCompactSupport_iterClassicalPartial (d := dimE) m idx hu_cpt
    have h_w_Ω'' : tsupport (iterClassicalPartial (d := dimE) m idx u) ⊆ Ω'' :=
      (tsupport_iterClassicalPartial_subset (d := dimE) m idx
        (isClosed_tsupport u) (subset_refl _)).trans hu_Ω''
    have h_s_cd : ContDiff ℝ (⊤ : ℕ∞)
        (iteratedPerturbedSource (d := dimE) B m u RHS idx) :=
      contDiff_iteratedPerturbedSource (d := dimE) B m hu_cd hRHS_cd idx
    have h_s_Ω'' : tsupport (iteratedPerturbedSource (d := dimE) B m u RHS idx)
        ⊆ Ω'' :=
      (tsupport_iteratedPerturbedSource_subset (d := dimE) B m
        ((isClosed_tsupport u).union (isClosed_tsupport RHS))
        subset_union_left subset_union_right idx).trans
        (Set.union_subset hu_Ω'' (hRHS_u.trans hu_Ω''))
    have h_s_cpt : HasCompactSupport
        (iteratedPerturbedSource (d := dimE) B m u RHS idx) :=
      HasCompactSupport.of_support_subset_isCompact
        hΩ''_compact_closure
        (fun x hx => subset_closure (h_s_Ω'' (subset_tsupport _ hx)))
    have h_wrap := hCw h_weak_sol h_w_cpt h_s_cd h_s_cpt h_w_Ω'' h_s_Ω''
    have h_w1_le : iteratedWeakSobolevNorm (d := dimE) 1 2
        (iterClassicalPartial (d := dimE) m idx u) Ω'' ≤
        iteratedWeakSobolevNorm (d := dimE) (m + 1) 2 u Ω'' := by
      have h := wkpNorm_iterClassicalPartial_le (d := dimE) hΩ''_open 1 m idx
        hu_cd hu_cpt
      rwa [show m + 1 = m + 1 from rfl] at h
    have h_s0_le : iteratedWeakSobolevNorm (d := dimE) 0 2
        (iteratedPerturbedSource (d := dimE) B m u RHS idx) Ω'' ≤
        ENNReal.ofReal Cs *
          (iteratedWeakSobolevNorm (d := dimE) m 2 RHS Ω'' +
            iteratedWeakSobolevNorm (d := dimE) (m + 1) 2 u Ω'') :=
      hCs hu_cd hu_cpt hRHS_cd hRHS_cpt idx
    refine h_wrap.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
    calc iteratedWeakSobolevNorm (d := dimE) 1 2 (iterClassicalPartial (d := dimE) m idx u) Ω'' +
          iteratedWeakSobolevNorm (d := dimE) 0 2
            (iteratedPerturbedSource (d := dimE) B m u RHS idx) Ω''
        ≤ iteratedWeakSobolevNorm (d := dimE) (m + 1) 2 u Ω'' +
            ENNReal.ofReal Cs *
              (iteratedWeakSobolevNorm (d := dimE) m 2 RHS Ω'' +
                iteratedWeakSobolevNorm (d := dimE) (m + 1) 2 u Ω'') :=
          add_le_add h_w1_le h_s0_le
      _ ≤ (ENNReal.ofReal Cs + 1) *
            (iteratedWeakSobolevNorm (d := dimE) m 2 RHS Ω'' +
              iteratedWeakSobolevNorm (d := dimE) (m + 1) 2 u Ω'') := by
          rw [add_mul, one_mul, add_comm]
          exact add_le_add le_rfl le_add_self
  have h_sum_partial :
      ∑ idx : Fin m → Fin dimE,
        iteratedWeakSobolevNorm (d := dimE) 2 2 (iterClassicalPartial (d := dimE) m idx u) Ω'' ≤
      ∑ _idx : Fin m → Fin dimE,
        ENNReal.ofReal Cw *
          ((ENNReal.ofReal Cs + 1) *
            (iteratedWeakSobolevNorm (d := dimE) m 2 RHS Ω'' +
              iteratedWeakSobolevNorm (d := dimE) (m + 1) 2 u Ω'')) :=
    Finset.sum_le_sum (fun idx _ => h_partial_le idx)
  refine h_assembly.trans ?_
  set DR : ℝ≥0∞ :=
    iteratedWeakSobolevNorm (d := dimE) m 2 RHS Ω'' + iteratedWeakSobolevNorm (d := dimE) (m + 1) 2 u Ω''
    with hDR_def
  have h_card_sum :
      ∑ _idx : Fin m → Fin dimE,
        ENNReal.ofReal Cw * ((ENNReal.ofReal Cs + 1) * DR) =
      (dimE ^ m : ℕ) *
        (ENNReal.ofReal Cw * ((ENNReal.ofReal Cs + 1) * DR)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul]
  have h_sum_le :
      ∑ idx : Fin m → Fin dimE,
        iteratedWeakSobolevNorm (d := dimE) 2 2 (iterClassicalPartial (d := dimE) m idx u) Ω'' ≤
      (dimE ^ m : ℕ) *
        (ENNReal.ofReal Cw * ((ENNReal.ofReal Cs + 1) * DR)) := by
    refine h_sum_partial.trans (le_of_eq ?_)
    rw [h_card_sum]
  refine (add_le_add h_sum_le (le_refl _)).trans ?_
  have h_first_eq :
      (dimE ^ m : ℕ) *
        (ENNReal.ofReal Cw * ((ENNReal.ofReal Cs + 1) * DR)) =
      ENNReal.ofReal (((dimE : ℝ) ^ m) * Cw * (Cs + 1)) * DR := by
    rw [show ((dimE ^ m : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((dimE : ℝ) ^ m) from by
        rw [← ENNReal.ofReal_natCast, Nat.cast_pow],
      show (ENNReal.ofReal Cs + 1) = ENNReal.ofReal (Cs + 1) from by
        rw [ENNReal.ofReal_add hCs_nn (by norm_num : (0 : ℝ) ≤ 1),
          ENNReal.ofReal_one],
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    ring
  have h_u_le_DR : iteratedWeakSobolevNorm (d := dimE) (m + 1) 2 u Ω'' ≤ DR := by
    rw [hDR_def]; exact le_add_self
  calc (dimE ^ m : ℕ) *
        (ENNReal.ofReal Cw * ((ENNReal.ofReal Cs + 1) * DR)) +
        N * iteratedWeakSobolevNorm (d := dimE) (m + 1) 2 u Ω''
      = ENNReal.ofReal (((dimE : ℝ) ^ m) * Cw * (Cs + 1)) * DR +
          ENNReal.ofReal N.toReal * iteratedWeakSobolevNorm (d := dimE) (m + 1) 2 u Ω'' := by
        rw [h_first_eq, ← hN_eq]
    _ ≤ ENNReal.ofReal (((dimE : ℝ) ^ m) * Cw * (Cs + 1)) * DR +
          ENNReal.ofReal N.toReal * DR :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left h_u_le_DR (zero_le _))
    _ = ENNReal.ofReal
          (((dimE : ℝ) ^ m) * Cw * (Cs + 1) + N.toReal) * DR := by
        rw [← add_mul,
          ← ENNReal.ofReal_add (by positivity) hN_toReal_nn]

set_option maxHeartbeats 1600000 in

theorem tensorComponent_aPriori_succ_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (m : ℕ)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (hΩ''_target : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hK_Ω'' : K ⊆ Ω'') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T F : SmoothCcTensor g r s),
      tsupport T.toFun ⊆ (chartAt H α).source →
      tsupport F.toFun ⊆ (chartAt H α).source →
      (∀ P : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
      (∀ Q : CompIdx E r s,
        tsupport (tensorComponentEuclid (I := I) (M := M) g r s F α Q) ⊆ K) →
      (∀ v : SmoothCcTensor g r s,
        ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) →
      (∑ P : CompIdx E r s,
        iteratedWeakSobolevNorm (d := dimE) (m + 2) 2
          (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') ≤
        ENNReal.ofReal C *
          ((∑ Q : CompIdx E r s,
              iteratedWeakSobolevNorm (d := dimE) m 2
                (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') +
            ∑ P : CompIdx E r s,
              iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
                (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') := by
  classical
  have h_succ : ∀ P₀ : CompIdx E r s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T F : SmoothCcTensor g r s),
        tsupport T.toFun ⊆ (chartAt H α).source →
        tsupport F.toFun ⊆ (chartAt H α).source →
        (∀ P : CompIdx E r s,
          tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
        (∀ Q : CompIdx E r s,
          tsupport (tensorComponentEuclid (I := I) (M := M) g r s F α Q) ⊆ K) →
        (∀ v : SmoothCcTensor g r s,
          ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v x
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
            tensorL2Inner (I := I) (M := M) g r s F.toFun v.toFun) →
        iteratedWeakSobolevNorm (d := dimE) (m + 2) 2
            (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) Ω'' ≤
          ENNReal.ofReal C *
            (iteratedWeakSobolevNorm (d := dimE) m 2
                (tensorComponentWeakRHS (I := I) (M := M)
                  g r s T F α hK hK_target P₀) Ω'' +
              iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
                (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) Ω'') :=
    fun P₀ => tensorComponent_aPriori_succ (I := I) (M := M) g r s α hK
      hK_target m P₀ hΩ''_open hΩ''_compact_closure hK_Ω''
  choose Cstep hCstep_nn hCstep using h_succ
  have h_src : ∀ P₀ : CompIdx E r s, ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ (T F : SmoothCcTensor g r s),
        tsupport T.toFun ⊆ (chartAt H α).source →
        tsupport F.toFun ⊆ (chartAt H α).source →
        (∀ P : CompIdx E r s,
          tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P) ⊆ K) →
        (∀ Q : CompIdx E r s,
          tsupport (tensorComponentEuclid (I := I) (M := M) g r s F α Q) ⊆ K) →
        iteratedWeakSobolevNorm (d := dimE) m 2
            (tensorComponentWeakRHS (I := I) (M := M)
              g r s T F α hK hK_target P₀) Ω'' ≤
          ENNReal.ofReal Kc *
            ((∑ Q : CompIdx E r s,
                iteratedWeakSobolevNorm (d := dimE) m 2
                  (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'') +
              ∑ P : CompIdx E r s,
                iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
                  (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'') := by
    intro P₀
    obtain ⟨Kc, hKc_nn, hKc⟩ :=
      tensorComponentWeakRHS_wkpNorm_le (I := I) (M := M) g r s α hK hK_target
        m P₀
    refine ⟨Kc, hKc_nn, fun T F hT_supp hF_supp hT_K hF_K => ?_⟩
    exact hKc T F hT_supp hF_supp hT_K hF_K hΩ''_open hΩ''_target
  choose Ksrc hKsrc_nn hKsrc using h_src
  refine ⟨∑ P₀ : CompIdx E r s, (Cstep P₀) * (Ksrc P₀ + 1),
    Finset.sum_nonneg (fun P₀ _ =>
      mul_nonneg (hCstep_nn P₀) (by linarith [hKsrc_nn P₀])), ?_⟩
  intro T F hT_supp hF_supp hT_K hF_K hweak
  set SF : ℝ≥0∞ := ∑ Q : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) m 2
    (tensorComponentEuclid (I := I) (M := M) g r s F α Q) Ω'' with hSF_def
  set ST : ℝ≥0∞ := ∑ P : CompIdx E r s, iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
    (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'' with hST_def
  have h_per : ∀ P₀ : CompIdx E r s,
      iteratedWeakSobolevNorm (d := dimE) (m + 2) 2
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) Ω'' ≤
        ENNReal.ofReal ((Cstep P₀) * (Ksrc P₀ + 1)) * (SF + ST) := by
    intro P₀
    have h_step := hCstep P₀ T F hT_supp hF_supp hT_K hF_K hweak
    have h_source := hKsrc P₀ T F hT_supp hF_supp hT_K hF_K
    rw [← hSF_def, ← hST_def] at h_source
    have h_u_le_ST : iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) Ω'' ≤ ST :=
      Finset.single_le_sum
        (f := fun P : CompIdx E r s => iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
          (tensorComponentEuclid (I := I) (M := M) g r s T α P) Ω'')
        (fun P _ => zero_le _) (Finset.mem_univ P₀)
    refine h_step.trans ?_
    rw [ENNReal.ofReal_mul (hCstep_nn P₀), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
    rw [show (ENNReal.ofReal (Ksrc P₀ + 1)) =
        ENNReal.ofReal (Ksrc P₀) + 1 from by
      rw [ENNReal.ofReal_add (hKsrc_nn P₀) (by norm_num : (0 : ℝ) ≤ 1),
        ENNReal.ofReal_one]]
    calc iteratedWeakSobolevNorm (d := dimE) m 2
            (tensorComponentWeakRHS (I := I) (M := M)
              g r s T F α hK hK_target P₀) Ω'' +
          iteratedWeakSobolevNorm (d := dimE) (m + 1) 2
            (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) Ω''
        ≤ ENNReal.ofReal (Ksrc P₀) * (SF + ST) + (SF + ST) :=
          add_le_add h_source
            (h_u_le_ST.trans (le_add_self : ST ≤ SF + ST))
      _ = (ENNReal.ofReal (Ksrc P₀) + 1) * (SF + ST) := by
          rw [add_mul, one_mul]
  refine (Finset.sum_le_sum (fun P₀ _ => h_per P₀)).trans ?_
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
    (fun P₀ _ => mul_nonneg (hCstep_nn P₀) (by linarith [hKsrc_nn P₀]))]

end TensorAPriori

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry

end
