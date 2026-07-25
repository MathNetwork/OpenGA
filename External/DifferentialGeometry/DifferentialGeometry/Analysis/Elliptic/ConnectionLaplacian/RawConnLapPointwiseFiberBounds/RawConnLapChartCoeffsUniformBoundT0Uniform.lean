import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapChartCoordFormulaT0Linear
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapPointwiseFiberBounds.RawConnLapChartCoeffsUniformBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapPointwiseFiberBounds.RawConnLapRiemannianFiberNormSqLeChartData


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_sq_le_fderiv_sq
    {f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (m : Fin (Module.finrank ℝ E)) :
    (euclidPartial (E := E) m f y) ^ 2 ≤ ‖fderiv ℝ f y‖ ^ 2 := by
  classical
  set em : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := EuclideanSpace.single m 1
  have h_norm_em : ‖em‖ = 1 := by simp [em]
  have h_value : euclidPartial (E := E) m f y = fderiv ℝ f y em := rfl
  have h_opNorm : ‖fderiv ℝ f y em‖ ≤ ‖fderiv ℝ f y‖ * ‖em‖ :=
    (fderiv ℝ f y).le_opNorm em
  have h_abs : |euclidPartial (E := E) m f y| ≤ ‖fderiv ℝ f y‖ := by
    rw [h_value]
    have h := h_opNorm
    rw [h_norm_em, mul_one] at h
    have : ‖fderiv ℝ f y em‖ = |fderiv ℝ f y em| := rfl
    rw [this] at h
    exact h
  have h_sq : (euclidPartial (E := E) m f y) ^ 2 =
      |euclidPartial (E := E) m f y| ^ 2 := (sq_abs _).symm
  rw [h_sq]
  exact pow_le_pow_left₀ (abs_nonneg _) h_abs 2

theorem rawTensorConnLap_chartα_coeffs_uniform_bound_on_pouTsupport_T0_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (idx : Fin r → Fin (Module.finrank ℝ E))
    (jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T₀ : SmoothCcTensor g r s),
        ∀ (b : M),
          b ∈ tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            chartLeviCivitaGoodSet (I := I) α →
          (tensorChartComponentRaw (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s T₀) α idx jdx b) ^ 2 ≤
            K * (∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
                  ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
                    ((‖iteratedFDeriv ℝ 2
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M) g r s
                            T₀ α Idx' Jdx'))
                        ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
                    (‖fderiv ℝ
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M) g r s
                            T₀ α Idx' Jdx'))
                        ((toEuclidean (E := E)) ((extChartAt I α) b))‖) ^ 2 +
                    (chartPushedRaw I α
                       (tensorChartComponentRaw (I := I) (M := M) g r s
                         T₀ α Idx' Jdx')
                       ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2)) := by
  classical
  let n : ℕ := Module.finrank ℝ E
  have hn_def : n = Module.finrank ℝ E := rfl
  let cardI : ℕ := Fintype.card (Fin r → Fin (Module.finrank ℝ E))
  have hcardI_def : cardI = Fintype.card (Fin r → Fin (Module.finrank ℝ E)) := rfl
  let cardJ : ℕ := Fintype.card (Fin s → Fin (Module.finrank ℝ E))
  have hcardJ_def : cardJ = Fintype.card (Fin s → Fin (Module.finrank ℝ E)) := rfl
  set K_set : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    (fun b : M => (toEuclidean (E := E)) ((extChartAt I α) b)) ''
      tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_image_isCompact (I := I) (M := M) α
  have hK_sub : K_set ⊆ chartTargetEuclid (I := I) (M := M) α :=
    pouTsupport_image_subset_chartTargetEuclid (I := I) (M := M) α
  obtain ⟨C_2, C_1, C_0, hC2_cd, hC1_cd, hC0_cd, hformula⟩ :=
    rawTensorConnLap_chartα_raw_eq_T₀_linear_formula
      (I := I) (M := M) g r s α idx jdx
  have h_each_C2 : ∀ kl : Fin n × Fin n, ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ K_set, |C_2 kl.1 kl.2 y| ≤ C := by
    intro kl
    exact exists_sup_bound_of_contDiffOn_on_compact_subset hK_compact hK_sub
      (hC2_cd kl.1 kl.2)
  choose C2_fn hC2_fn_nn hC2_fn_bd using h_each_C2
  have h_each_C1 : ∀ (q : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)) × Fin n),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ y ∈ K_set, |C_1 q.1 q.2.1 q.2.2 y| ≤ C := by
    intro q
    exact exists_sup_bound_of_contDiffOn_on_compact_subset hK_compact hK_sub
      (hC1_cd q.1 q.2.1 q.2.2)
  choose C1_fn hC1_fn_nn hC1_fn_bd using h_each_C1
  have h_each_C0 : ∀ (p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E))),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ y ∈ K_set, |C_0 p.1 p.2 y| ≤ C := by
    intro p
    exact exists_sup_bound_of_contDiffOn_on_compact_subset hK_compact hK_sub
      (hC0_cd p.1 p.2)
  choose C0_fn hC0_fn_nn hC0_fn_bd using h_each_C0
  set B2 : ℝ :=
    (Finset.univ : Finset (Fin n × Fin n)).sup' Finset.univ_nonempty C2_fn
    with hB2_def
  have hB2_nn : 0 ≤ B2 := by
    rcases Finset.univ_nonempty (α := Fin n × Fin n) with ⟨kl₀, _⟩
    exact (hC2_fn_nn kl₀).trans
      (Finset.le_sup'_of_le C2_fn (Finset.mem_univ kl₀) (le_refl _))
  have hB2_bd : ∀ k l : Fin n, ∀ y ∈ K_set, |C_2 k l y| ≤ B2 := by
    intro k l y hy
    have h := hC2_fn_bd ⟨k, l⟩ y hy
    exact h.trans
      (Finset.le_sup'_of_le C2_fn (Finset.mem_univ (⟨k, l⟩ : Fin n × Fin n))
        (le_refl _))
  set B1 : ℝ :=
    ((Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)) × Fin n))).sup'
      Finset.univ_nonempty C1_fn
    with hB1_def
  have hB1_nn : 0 ≤ B1 := by
    rcases Finset.univ_nonempty
      (α := (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)) × Fin n) with ⟨q₀, _⟩
    exact (hC1_fn_nn q₀).trans
      (Finset.le_sup'_of_le C1_fn (Finset.mem_univ q₀) (le_refl _))
  have hB1_bd : ∀ (I' : Fin r → Fin (Module.finrank ℝ E)) (J' : Fin s → Fin (Module.finrank ℝ E)) (m : Fin n),
      ∀ y ∈ K_set, |C_1 I' J' m y| ≤ B1 := by
    intro I' J' m y hy
    have h := hC1_fn_bd ⟨I', J', m⟩ y hy
    exact h.trans
      (Finset.le_sup'_of_le C1_fn
        (Finset.mem_univ (⟨I', J', m⟩ :
          (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)) × Fin n)) (le_refl _))
  set B0 : ℝ :=
    ((Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E))))).sup'
      Finset.univ_nonempty C0_fn
    with hB0_def
  have hB0_nn : 0 ≤ B0 := by
    rcases Finset.univ_nonempty
      (α := (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E))) with ⟨p₀, _⟩
    exact (hC0_fn_nn p₀).trans
      (Finset.le_sup'_of_le C0_fn (Finset.mem_univ p₀) (le_refl _))
  have hB0_bd : ∀ (I' : Fin r → Fin (Module.finrank ℝ E)) (J' : Fin s → Fin (Module.finrank ℝ E)),
      ∀ y ∈ K_set, |C_0 I' J' y| ≤ B0 := by
    intro I' J' y hy
    have h := hC0_fn_bd ⟨I', J'⟩ y hy
    exact h.trans
      (Finset.le_sup'_of_le C0_fn
        (Finset.mem_univ (⟨I', J'⟩ : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E))))
        (le_refl _))
  refine ⟨3 * ((n : ℝ) ^ 4 * B2 ^ 2 +
      (cardI : ℝ) * (cardJ : ℝ) * (n : ℝ) ^ 2 * B1 ^ 2 +
      (cardI : ℝ) * (cardJ : ℝ) * B0 ^ 2),
    by positivity, ?_⟩
  intro T₀ b hb_inter
  have hidentity := hformula T₀ hb_inter
  set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
  have hb_tsupp : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := hb_inter.1
  have hy_K : y ∈ K_set := ⟨b, hb_tsupp, rfl⟩
  have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := hK_sub hy_K
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hy_mem_nhds : (chartTargetEuclid (I := I) (M := M) α) ∈ nhds y :=
    h_open.mem_nhds hy_target
  set lhs : ℝ := tensorChartComponentRaw (I := I) (M := M) g r s
      (rawTensorConnLapSmooth (I := I) g r s T₀) α idx jdx b with hlhs_def
  set Block2 : ℝ := ∑ k : Fin n, ∑ l : Fin n,
      C_2 k l y *
        euclidPartial (E := E) l
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α idx jdx)))
          y
    with hBlock2_def
  set Block1 : ℝ := ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), ∑ m : Fin n,
      C_1 I' J' m y *
        euclidPartial (E := E) m
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J'))
          y
    with hBlock1_def
  set Block0 : ℝ := ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E),
      C_0 I' J' y *
        chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J') y
    with hBlock0_def
  have h_lhs_eq : lhs = Block2 + Block1 + Block0 := by
    simp only [hlhs_def, hBlock2_def, hBlock1_def, hBlock0_def, hy_def]
    exact hidentity
  set N_iter : (Fin r → Fin (Module.finrank ℝ E)) → (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun I' J' =>
      ‖iteratedFDeriv ℝ 2
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y‖
    with hN_iter_def
  set N_fd : (Fin r → Fin (Module.finrank ℝ E)) → (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun I' J' =>
      ‖fderiv ℝ (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y‖
    with hN_fd_def
  set R0 : (Fin r → Fin (Module.finrank ℝ E)) → (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun I' J' => chartPushedRaw I α
      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J') y
    with hR0_def
  set H : (Fin r → Fin (Module.finrank ℝ E)) → (Fin s → Fin (Module.finrank ℝ E)) → ℝ :=
    fun I' J' => (N_iter I' J') ^ 2 + (N_fd I' J') ^ 2 + (R0 I' J') ^ 2
    with hH_def
  have hH_nn : ∀ I' J', 0 ≤ H I' J' := by
    intro I' J'
    have h1 : 0 ≤ (N_iter I' J') ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (N_fd I' J') ^ 2 := sq_nonneg _
    have h3 : 0 ≤ (R0 I' J') ^ 2 := sq_nonneg _
    have h12 : 0 ≤ (N_iter I' J') ^ 2 + (N_fd I' J') ^ 2 :=
      add_nonneg h1 h2
    exact add_nonneg h12 h3
  set BigSum : ℝ := ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), H I' J'
    with hBigSum_def
  have hBigSum_nn : 0 ≤ BigSum :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => hH_nn _ _))
  have h_chartPushed_cd_at_2 : ∀ (I' : Fin r → Fin (Module.finrank ℝ E)) (J' : Fin s → Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ 2 (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y := by
    intro I' J'
    have h_inf : ContDiffAt ℝ ∞ (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y :=
      (chartPushedRaw_tensorChartComponentRaw_contDiffOn
        (I := I) (M := M) g r s T₀ α I' J').contDiffAt hy_mem_nhds
    apply h_inf.of_le
    decide
  set f_ij : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushedRaw I α
      (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α idx jdx)
    with hf_ij_def
  have h_Block2_abs : |Block2| ≤
      (n : ℝ) ^ 2 * B2 * ‖iteratedFDeriv ℝ 2 f_ij y‖ := by
    have h_each : ∀ k l : Fin n,
        |C_2 k l y *
          euclidPartial (E := E) l (euclidPartial (E := E) k f_ij) y| ≤
        B2 * ‖iteratedFDeriv ℝ 2 f_ij y‖ := by
      intro k l
      have h_C : |C_2 k l y| ≤ B2 := hB2_bd k l y hy_K
      have h_partial_sq :
          (euclidPartial (E := E) l (euclidPartial (E := E) k f_ij) y) ^ 2 ≤
            ‖iteratedFDeriv ℝ 2 f_ij y‖ ^ 2 :=
        euclidPartial_sq_le_iteratedFDeriv_two_sq
          (h_chartPushed_cd_at_2 idx jdx) k l
      have h_partial_abs :
          |euclidPartial (E := E) l (euclidPartial (E := E) k f_ij) y| ≤
            ‖iteratedFDeriv ℝ 2 f_ij y‖ := by
        have h_abs_sq : (|euclidPartial (E := E) l
              (euclidPartial (E := E) k f_ij) y|) ^ 2 ≤
            (‖iteratedFDeriv ℝ 2 f_ij y‖) ^ 2 := by
          rw [sq_abs]
          exact h_partial_sq
        exact (abs_le_of_sq_le_sq' h_abs_sq (norm_nonneg _)).2
      have h_mul := mul_le_mul h_C h_partial_abs (abs_nonneg _) hB2_nn
      rw [abs_mul]
      exact h_mul
    have h_sum_le :
        (∑ k : Fin n, ∑ l : Fin n,
          |C_2 k l y *
            euclidPartial (E := E) l (euclidPartial (E := E) k f_ij) y|) ≤
        ∑ k : Fin n, ∑ l : Fin n, B2 * ‖iteratedFDeriv ℝ 2 f_ij y‖ :=
      Finset.sum_le_sum (fun k _ =>
        Finset.sum_le_sum (fun l _ => h_each k l))
    have h_sum_const :
        (∑ _k : Fin n, ∑ _l : Fin n,
          B2 * ‖iteratedFDeriv ℝ 2 f_ij y‖) =
          (n : ℝ) ^ 2 * B2 * ‖iteratedFDeriv ℝ 2 f_ij y‖ := by
      rw [Finset.sum_const, Finset.sum_const]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have h_abs_block2_le :
        |Block2| ≤ ∑ k : Fin n, ∑ l : Fin n,
          |C_2 k l y *
            euclidPartial (E := E) l (euclidPartial (E := E) k f_ij) y| := by
      rw [hBlock2_def]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      exact Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs _ _)
    calc |Block2|
        ≤ ∑ k : Fin n, ∑ l : Fin n,
            |C_2 k l y *
              euclidPartial (E := E) l
                (euclidPartial (E := E) k f_ij) y| := h_abs_block2_le
      _ ≤ ∑ k : Fin n, ∑ l : Fin n,
            B2 * ‖iteratedFDeriv ℝ 2 f_ij y‖ := h_sum_le
      _ = (n : ℝ) ^ 2 * B2 * ‖iteratedFDeriv ℝ 2 f_ij y‖ := h_sum_const
  have h_Block2_sq : Block2 ^ 2 ≤
      (n : ℝ) ^ 4 * B2 ^ 2 * ‖iteratedFDeriv ℝ 2 f_ij y‖ ^ 2 := by
    have h_abs_sq : Block2 ^ 2 = |Block2| ^ 2 := (sq_abs _).symm
    rw [h_abs_sq]
    have h_sq_le :
        |Block2| ^ 2 ≤ ((n : ℝ) ^ 2 * B2 * ‖iteratedFDeriv ℝ 2 f_ij y‖) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h_Block2_abs 2
    refine h_sq_le.trans ?_
    have : ((n : ℝ) ^ 2 * B2 * ‖iteratedFDeriv ℝ 2 f_ij y‖) ^ 2 =
        (n : ℝ) ^ 4 * B2 ^ 2 * ‖iteratedFDeriv ℝ 2 f_ij y‖ ^ 2 := by ring
    rw [this]
  have h_Block1_abs : |Block1| ≤
      B1 * ((n : ℝ) *
        ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), N_fd I' J') := by
    have h_each : ∀ (I' : Fin r → Fin (Module.finrank ℝ E)) (J' : Fin s → Fin (Module.finrank ℝ E)) (m : Fin n),
        |C_1 I' J' m y *
          euclidPartial (E := E) m
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α I' J')) y| ≤
          B1 * N_fd I' J' := by
      intro I' J' m
      have h_C : |C_1 I' J' m y| ≤ B1 := hB1_bd I' J' m y hy_K
      have h_p_sq :
          (euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s
                  T₀ α I' J')) y) ^ 2 ≤
            ‖fderiv ℝ (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s
                T₀ α I' J')) y‖ ^ 2 :=
        euclidPartial_sq_le_fderiv_sq m
      have h_p_abs :
          |euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s
                  T₀ α I' J')) y| ≤
            ‖fderiv ℝ (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s
                T₀ α I' J')) y‖ := by
        have h_abs_sq :
            (|euclidPartial (E := E) m
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s
                    T₀ α I' J')) y|) ^ 2 ≤
              ‖fderiv ℝ (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s
                  T₀ α I' J')) y‖ ^ 2 := by
          rw [sq_abs]; exact h_p_sq
        exact (abs_le_of_sq_le_sq' h_abs_sq (norm_nonneg _)).2
      have h_mul := mul_le_mul h_C h_p_abs (abs_nonneg _) hB1_nn
      rw [abs_mul]
      exact h_mul
    have h_abs_block1_le :
        |Block1| ≤ ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), ∑ m : Fin n,
          |C_1 I' J' m y *
            euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s
                  T₀ α I' J')) y| := by
      rw [hBlock1_def]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine Finset.sum_le_sum (fun I' _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      exact Finset.sum_le_sum (fun J' _ => Finset.abs_sum_le_sum_abs _ _)
    have h_sum_le :
        (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), ∑ m : Fin n,
          |C_1 I' J' m y *
            euclidPartial (E := E) m
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s
                  T₀ α I' J')) y|) ≤
        ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), ∑ _m : Fin n,
          B1 * N_fd I' J' :=
      Finset.sum_le_sum (fun I' _ =>
        Finset.sum_le_sum (fun J' _ =>
          Finset.sum_le_sum (fun m _ => h_each I' J' m)))
    have h_inner_sum :
        ∀ (I' : Fin r → Fin (Module.finrank ℝ E)) (J' : Fin s → Fin (Module.finrank ℝ E)),
          (∑ _m : Fin n, B1 * N_fd I' J') = (n : ℝ) * (B1 * N_fd I' J') := by
      intro I' J'
      rw [Finset.sum_const]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h_rewrite :
        (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), ∑ _m : Fin n,
          B1 * N_fd I' J') =
        B1 * ((n : ℝ) *
          ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), N_fd I' J') := by
      have h_step :
          (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), ∑ _m : Fin n,
            B1 * N_fd I' J') =
          ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            (n : ℝ) * (B1 * N_fd I' J') := by
        refine Finset.sum_congr rfl (fun I' _ => ?_)
        refine Finset.sum_congr rfl (fun J' _ => ?_)
        exact h_inner_sum I' J'
      have h_step2 :
          (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            (n : ℝ) * (B1 * N_fd I' J')) =
          B1 * ((n : ℝ) *
            ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), N_fd I' J') := by
        have h_a : (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            (n : ℝ) * (B1 * N_fd I' J')) =
            ((n : ℝ) * B1) *
              ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), N_fd I' J' := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun I' _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun J' _ => ?_)
          ring
        rw [h_a]; ring
      rw [h_step, h_step2]
    calc |Block1|
        ≤ ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), ∑ m : Fin n,
            |C_1 I' J' m y *
              euclidPartial (E := E) m
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s
                    T₀ α I' J')) y| := h_abs_block1_le
      _ ≤ ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), ∑ _m : Fin n,
            B1 * N_fd I' J' := h_sum_le
      _ = B1 * ((n : ℝ) *
            ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), N_fd I' J') := h_rewrite
  have h_Block0_abs : |Block0| ≤
      B0 * (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), |R0 I' J'|) := by
    have h_each : ∀ (I' : Fin r → Fin (Module.finrank ℝ E)) (J' : Fin s → Fin (Module.finrank ℝ E)),
        |C_0 I' J' y * R0 I' J'| ≤ B0 * |R0 I' J'| := by
      intro I' J'
      have h_C : |C_0 I' J' y| ≤ B0 := hB0_bd I' J' y hy_K
      have h_mul := mul_le_mul h_C (le_refl |R0 I' J'|) (abs_nonneg _) hB0_nn
      rw [abs_mul]
      exact h_mul
    have h_abs_block0_le :
        |Block0| ≤ ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E),
          |C_0 I' J' y * R0 I' J'| := by
      rw [hBlock0_def]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      exact Finset.sum_le_sum (fun I' _ => Finset.abs_sum_le_sum_abs _ _)
    have h_sum_le :
        ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), |C_0 I' J' y * R0 I' J'| ≤
        ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), B0 * |R0 I' J'| :=
      Finset.sum_le_sum (fun I' _ =>
        Finset.sum_le_sum (fun J' _ => h_each I' J'))
    have h_sum_factor :
        (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), B0 * |R0 I' J'|) =
        B0 * (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), |R0 I' J'|) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun I' _ => ?_)
      rw [Finset.mul_sum]
    calc |Block0|
        ≤ ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            |C_0 I' J' y * R0 I' J'| := h_abs_block0_le
      _ ≤ ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            B0 * |R0 I' J'| := h_sum_le
      _ = B0 * (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), |R0 I' J'|) :=
          h_sum_factor
  have h_lhs_sq_le : lhs ^ 2 ≤
      3 * (Block2 ^ 2 + Block1 ^ 2 + Block0 ^ 2) := by
    rw [h_lhs_eq]
    nlinarith [sq_nonneg (Block2 - Block1), sq_nonneg (Block2 - Block0),
      sq_nonneg (Block1 - Block0)]
  set S_iter : ℝ := ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E),
      (N_iter I' J') ^ 2 with hS_iter_def
  set S_fd : ℝ := ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E),
      (N_fd I' J') ^ 2 with hS_fd_def
  set S_raw : ℝ := ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E),
      (R0 I' J') ^ 2 with hS_raw_def
  have hS_iter_nn : 0 ≤ S_iter :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hS_fd_nn : 0 ≤ S_fd :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hS_raw_nn : 0 ≤ S_raw :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hBigSum_eq : BigSum = S_iter + S_fd + S_raw := by
    simp only [hBigSum_def, hH_def, hS_iter_def, hS_fd_def, hS_raw_def,
      ← Finset.sum_add_distrib]
  have h_iter_dom_f_ij :
      ‖iteratedFDeriv ℝ 2 f_ij y‖ ^ 2 ≤ S_iter := by
    have h_le_inner :
        (N_iter idx jdx) ^ 2 ≤ ∑ J' : Fin s → Fin (Module.finrank ℝ E), (N_iter idx J') ^ 2 :=
      Finset.single_le_sum (f := fun J' => (N_iter idx J') ^ 2)
        (s := (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))))
        (fun _ _ => sq_nonneg _) (Finset.mem_univ jdx)
    have h_le_outer :
        (∑ J' : Fin s → Fin (Module.finrank ℝ E), (N_iter idx J') ^ 2) ≤ S_iter :=
      Finset.single_le_sum
        (f := fun I' => ∑ J' : Fin s → Fin (Module.finrank ℝ E), (N_iter I' J') ^ 2)
        (s := (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))))
        (fun I' _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (Finset.mem_univ idx)
    have h_eq_LHS :
        ‖iteratedFDeriv ℝ 2 f_ij y‖ ^ 2 = (N_iter idx jdx) ^ 2 := by
      simp only [hf_ij_def, hN_iter_def]
    rw [h_eq_LHS]
    exact h_le_inner.trans h_le_outer
  have h_Block2_via_S : Block2 ^ 2 ≤ (n : ℝ) ^ 4 * B2 ^ 2 * S_iter := by
    have h_nn : 0 ≤ (n : ℝ) ^ 4 * B2 ^ 2 := by positivity
    exact h_Block2_sq.trans
      (mul_le_mul_of_nonneg_left h_iter_dom_f_ij h_nn)
  have h_Block1_via_S : Block1 ^ 2 ≤
      (cardI : ℝ) * (cardJ : ℝ) * (n : ℝ) ^ 2 * B1 ^ 2 * S_fd := by
    have hN_fd_sum_nn :
        0 ≤ ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), N_fd I' J' :=
      Finset.sum_nonneg (fun _ _ =>
        Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    have h_step1 : Block1 ^ 2 ≤
        (B1 * ((n : ℝ) *
          ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), N_fd I' J')) ^ 2 := by
      rw [show Block1 ^ 2 = |Block1| ^ 2 from (sq_abs _).symm]
      exact pow_le_pow_left₀ (abs_nonneg _) h_Block1_abs 2
    have h_cs : (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), N_fd I' J') ^ 2 ≤
        ((cardI : ℝ) * (cardJ : ℝ)) * S_fd := by
      have h_card :
          ((Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ)
            = (cardI : ℝ) * (cardJ : ℝ) := by
        simp [cardI, cardJ, Fintype.card_prod]
      have h_prod_sum_a :
          (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), N_fd I' J') =
          ∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), N_fd p.1 p.2 := by
        rw [← Finset.sum_product']; rfl
      have h_prod_sum_b : S_fd =
          ∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), N_fd p.1 p.2 ^ 2 := by
        simp only [hS_fd_def]
        rw [← Finset.sum_product']; rfl
      rw [h_prod_sum_a, h_prod_sum_b]
      have h_cs_simple :
          (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), (1 : ℝ) * N_fd p.1 p.2) ^ 2 ≤
          (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), (1 : ℝ) ^ 2) *
          (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), N_fd p.1 p.2 ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq
          (Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E))))
          (fun _ => (1 : ℝ)) (fun p => N_fd p.1 p.2)
      have h_lhs_eq2 :
          (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), (1 : ℝ) * N_fd p.1 p.2) =
          (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), N_fd p.1 p.2) := by
        refine Finset.sum_congr rfl (fun p _ => ?_); ring
      have h_const_eq :
          (∑ _p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), (1 : ℝ) ^ 2) =
          (Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)))).card := by
        rw [Finset.sum_const]; simp
      rw [h_lhs_eq2] at h_cs_simple
      rw [h_const_eq] at h_cs_simple
      rw [h_card] at h_cs_simple
      exact h_cs_simple
    have h_expand : (B1 * ((n : ℝ) *
        ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), N_fd I' J')) ^ 2 =
        B1 ^ 2 * (n : ℝ) ^ 2 *
          (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), N_fd I' J') ^ 2 := by
      ring
    calc Block1 ^ 2
        ≤ (B1 * ((n : ℝ) *
            ∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), N_fd I' J')) ^ 2 := h_step1
      _ = B1 ^ 2 * (n : ℝ) ^ 2 *
            (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), N_fd I' J') ^ 2 := h_expand
      _ ≤ B1 ^ 2 * (n : ℝ) ^ 2 *
            ((cardI : ℝ) * (cardJ : ℝ) * S_fd) := by
            have h_nn : 0 ≤ B1 ^ 2 * (n : ℝ) ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_left h_cs h_nn
      _ = (cardI : ℝ) * (cardJ : ℝ) * (n : ℝ) ^ 2 * B1 ^ 2 * S_fd := by ring
  have h_Block0_via_S : Block0 ^ 2 ≤
      (cardI : ℝ) * (cardJ : ℝ) * B0 ^ 2 * S_raw := by
    have h_step1 : Block0 ^ 2 ≤
        (B0 * (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), |R0 I' J'|)) ^ 2 := by
      rw [show Block0 ^ 2 = |Block0| ^ 2 from (sq_abs _).symm]
      exact pow_le_pow_left₀ (abs_nonneg _) h_Block0_abs 2
    have h_cs :
        (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), |R0 I' J'|) ^ 2 ≤
        ((cardI : ℝ) * (cardJ : ℝ)) * S_raw := by
      have h_card :
          ((Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)))).card : ℝ)
            = (cardI : ℝ) * (cardJ : ℝ) := by
        simp [cardI, cardJ, Fintype.card_prod]
      have h_prod_sum_a :
          (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), |R0 I' J'|) =
          ∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), |R0 p.1 p.2| := by
        rw [← Finset.sum_product']; rfl
      have h_prod_sum_b : S_raw =
          ∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), R0 p.1 p.2 ^ 2 := by
        simp only [hS_raw_def]
        rw [← Finset.sum_product']; rfl
      rw [h_prod_sum_a, h_prod_sum_b]
      have h_cs_simple :
          (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), (1 : ℝ) * |R0 p.1 p.2|) ^ 2 ≤
          (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), (1 : ℝ) ^ 2) *
          (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), |R0 p.1 p.2| ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq
          (Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E))))
          (fun _ => (1 : ℝ)) (fun p => |R0 p.1 p.2|)
      have h_lhs_eq2 :
          (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), (1 : ℝ) * |R0 p.1 p.2|) =
          (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), |R0 p.1 p.2|) := by
        refine Finset.sum_congr rfl (fun p _ => ?_); ring
      have h_const_eq :
          (∑ _p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), (1 : ℝ) ^ 2) =
          (Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)))).card := by
        rw [Finset.sum_const]; simp
      have h_sq_abs :
          (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), |R0 p.1 p.2| ^ 2) =
          (∑ p : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)), R0 p.1 p.2 ^ 2) := by
        refine Finset.sum_congr rfl (fun p _ => ?_); rw [sq_abs]
      rw [h_lhs_eq2] at h_cs_simple
      rw [h_const_eq] at h_cs_simple
      rw [h_sq_abs] at h_cs_simple
      rw [h_card] at h_cs_simple
      exact h_cs_simple
    have h_expand : (B0 * (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E),
        |R0 I' J'|)) ^ 2 =
        B0 ^ 2 *
          (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E), |R0 I' J'|) ^ 2 := by
      ring
    calc Block0 ^ 2
        ≤ (B0 * (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E),
            |R0 I' J'|)) ^ 2 := h_step1
      _ = B0 ^ 2 *
            (∑ I' : Fin r → Fin (Module.finrank ℝ E), ∑ J' : Fin s → Fin (Module.finrank ℝ E),
              |R0 I' J'|) ^ 2 := h_expand
      _ ≤ B0 ^ 2 *
            ((cardI : ℝ) * (cardJ : ℝ) * S_raw) := by
            have h_nn : 0 ≤ B0 ^ 2 := sq_nonneg _
            exact mul_le_mul_of_nonneg_left h_cs h_nn
      _ = (cardI : ℝ) * (cardJ : ℝ) * B0 ^ 2 * S_raw := by ring
  have h_S_iter_le_BigSum : S_iter ≤ BigSum := by
    rw [hBigSum_eq]; linarith [hS_fd_nn, hS_raw_nn]
  have h_S_fd_le_BigSum : S_fd ≤ BigSum := by
    rw [hBigSum_eq]; linarith [hS_iter_nn, hS_raw_nn]
  have h_S_raw_le_BigSum : S_raw ≤ BigSum := by
    rw [hBigSum_eq]; linarith [hS_iter_nn, hS_fd_nn]
  have h_Block2_BigSum : Block2 ^ 2 ≤ (n : ℝ) ^ 4 * B2 ^ 2 * BigSum := by
    have h_nn : 0 ≤ (n : ℝ) ^ 4 * B2 ^ 2 := by positivity
    exact h_Block2_via_S.trans
      (mul_le_mul_of_nonneg_left h_S_iter_le_BigSum h_nn)
  have h_Block1_BigSum : Block1 ^ 2 ≤
      (cardI : ℝ) * (cardJ : ℝ) * (n : ℝ) ^ 2 * B1 ^ 2 * BigSum := by
    have h_nn : 0 ≤ (cardI : ℝ) * (cardJ : ℝ) * (n : ℝ) ^ 2 * B1 ^ 2 := by
      positivity
    exact h_Block1_via_S.trans
      (mul_le_mul_of_nonneg_left h_S_fd_le_BigSum h_nn)
  have h_Block0_BigSum : Block0 ^ 2 ≤
      (cardI : ℝ) * (cardJ : ℝ) * B0 ^ 2 * BigSum := by
    have h_nn : 0 ≤ (cardI : ℝ) * (cardJ : ℝ) * B0 ^ 2 := by positivity
    exact h_Block0_via_S.trans
      (mul_le_mul_of_nonneg_left h_S_raw_le_BigSum h_nn)
  have h_sum_blocks : Block2 ^ 2 + Block1 ^ 2 + Block0 ^ 2 ≤
      ((n : ℝ) ^ 4 * B2 ^ 2 +
        (cardI : ℝ) * (cardJ : ℝ) * (n : ℝ) ^ 2 * B1 ^ 2 +
        (cardI : ℝ) * (cardJ : ℝ) * B0 ^ 2) * BigSum := by
    have h_expand : ((n : ℝ) ^ 4 * B2 ^ 2 +
        (cardI : ℝ) * (cardJ : ℝ) * (n : ℝ) ^ 2 * B1 ^ 2 +
        (cardI : ℝ) * (cardJ : ℝ) * B0 ^ 2) * BigSum =
      (n : ℝ) ^ 4 * B2 ^ 2 * BigSum +
      (cardI : ℝ) * (cardJ : ℝ) * (n : ℝ) ^ 2 * B1 ^ 2 * BigSum +
      (cardI : ℝ) * (cardJ : ℝ) * B0 ^ 2 * BigSum := by ring
    rw [h_expand]
    linarith
  have h_final : lhs ^ 2 ≤
      3 * ((n : ℝ) ^ 4 * B2 ^ 2 +
        (cardI : ℝ) * (cardJ : ℝ) * (n : ℝ) ^ 2 * B1 ^ 2 +
        (cardI : ℝ) * (cardJ : ℝ) * B0 ^ 2) * BigSum := by
    calc lhs ^ 2
        ≤ 3 * (Block2 ^ 2 + Block1 ^ 2 + Block0 ^ 2) := h_lhs_sq_le
      _ ≤ 3 * (((n : ℝ) ^ 4 * B2 ^ 2 +
            (cardI : ℝ) * (cardJ : ℝ) * (n : ℝ) ^ 2 * B1 ^ 2 +
            (cardI : ℝ) * (cardJ : ℝ) * B0 ^ 2) * BigSum) := by
            have h3 : (0 : ℝ) ≤ 3 := by norm_num
            exact mul_le_mul_of_nonneg_left h_sum_blocks h3
      _ = 3 * ((n : ℝ) ^ 4 * B2 ^ 2 +
            (cardI : ℝ) * (cardJ : ℝ) * (n : ℝ) ^ 2 * B1 ^ 2 +
            (cardI : ℝ) * (cardJ : ℝ) * B0 ^ 2) * BigSum := by ring
  exact h_final

end Connection
end Integral
end DifferentialGeometry

end
