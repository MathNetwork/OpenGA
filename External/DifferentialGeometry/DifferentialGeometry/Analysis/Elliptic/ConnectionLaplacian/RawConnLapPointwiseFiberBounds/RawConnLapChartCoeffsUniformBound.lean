import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapChartComponentSecondCovDerivFormula
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartSmooth
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.Defs


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
lemma pouTsupport_image_isCompact (α : M) :
    IsCompact
      ((fun b : M => (toEuclidean (E := E)) ((extChartAt I α) b)) ''
        tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  have h_tsupp_compact : IsCompact (tsupport
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    (isClosed_tsupport _).isCompact
  have h_tsupp_sub :
      tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
        (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source (I := I)]
    exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α hx
  have h_cont_extChart : ContinuousOn (extChartAt I α)
      (tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    (continuousOn_extChartAt α).mono h_tsupp_sub
  have h_image_compact : IsCompact ((extChartAt I α) ''
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    h_tsupp_compact.image_of_continuousOn h_cont_extChart
  have h_te_image_compact : IsCompact
      ((toEuclidean (E := E)) ''
        ((extChartAt I α) ''
          tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))) :=
    h_image_compact.image toEuclidean.continuous
  have h_image_eq :
      ((fun b : M => (toEuclidean (E := E)) ((extChartAt I α) b)) ''
        tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) =
      (toEuclidean (E := E)) ''
        ((extChartAt I α) ''
          tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
    rw [Set.image_image]
  rw [h_image_eq]
  exact h_te_image_compact

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
lemma pouTsupport_image_subset_chartTargetEuclid (α : M) :
    ((fun b : M => (toEuclidean (E := E)) ((extChartAt I α) b)) ''
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
  classical
  rintro y ⟨b, hb_tsupp, rfl⟩
  have hb_src : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
    exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate
      I M α hb_tsupp
  have hb_tgt : (extChartAt I α) b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_src
  exact ⟨(extChartAt I α) b, hb_tgt, rfl⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma exists_sup_bound_of_contDiffOn_on_compact_subset
    {U : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))}
    {K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))} (hK : IsCompact K)
    (hKU : K ⊆ U) {f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, |f y| ≤ C := by
  classical
  have hcont : ContinuousOn f U := hf.continuousOn
  have hcontK : ContinuousOn f K := hcont.mono hKU
  have hcontK_abs : ContinuousOn (fun y => |f y|) K := hcontK.abs
  rcases hK.bddAbove_image hcontK_abs with ⟨B, hB⟩
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro y hy
  exact (hB ⟨y, hy, rfl⟩).trans (le_max_left _ _)

theorem rawTensorConnLap_chartα_coeffs_uniform_bound_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (idx : Fin r → Fin (Module.finrank ℝ E))
    (jdx : Fin s → Fin (Module.finrank ℝ E))
    (T₀ : SmoothCcTensor g r s) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (b : M),
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        (tensorChartComponentRaw (I := I) (M := M) g r s
              (rawTensorConnLapSmooth (I := I) g r s T₀) α idx jdx b) ^ 2 ≤
          K * (∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  (euclidPartial (E := E) l
                    (euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw
                          (I := I) (M := M) g r s T₀ α idx jdx)))
                    ((toEuclidean (E := E)) ((extChartAt I α) b))) ^ 2 + 1) := by
  classical
  let n : ℕ := Module.finrank ℝ E
  have hn_def : n = Module.finrank ℝ E := rfl
  set K_set : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    (fun b : M => (toEuclidean (E := E)) ((extChartAt I α) b)) ''
      tsupport (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_image_isCompact (I := I) (M := M) α
  have hK_sub : K_set ⊆ chartTargetEuclid (I := I) (M := M) α :=
    pouTsupport_image_subset_chartTargetEuclid (I := I) (M := M) α
  have h_each_C : ∀ kl : Fin n × Fin n, ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ K_set,
        |weightedInvGramEuclid (I := I) (M := M) g α kl.1 kl.2 y| ≤ C := by
    intro kl
    exact exists_sup_bound_of_contDiffOn_on_compact_subset hK_compact hK_sub
      (weightedInvGramEuclid_contDiffOn (I := I) (M := M) g α kl.1 kl.2)
  choose C_fn hC_fn_nn hC_fn_bd using h_each_C
  set B_C : ℝ :=
    (Finset.univ : Finset (Fin n × Fin n)).sup' Finset.univ_nonempty C_fn
    with hB_C_def
  have hB_C_nn : 0 ≤ B_C := by
    rcases Finset.univ_nonempty (α := Fin n × Fin n) with ⟨kl₀, _⟩
    exact (hC_fn_nn kl₀).trans
      (Finset.le_sup'_of_le C_fn (Finset.mem_univ kl₀) (le_refl _))
  have hB_C_bd : ∀ k l : Fin n, ∀ y ∈ K_set,
      |weightedInvGramEuclid (I := I) (M := M) g α k l y| ≤ B_C := by
    intro k l y hy
    have h := hC_fn_bd ⟨k, l⟩ y hy
    refine h.trans ?_
    exact Finset.le_sup'_of_le C_fn (Finset.mem_univ (⟨k, l⟩ : Fin n × Fin n))
      (le_refl _)
  have h_chartPushed_raw_contDiffOn : ContDiffOn ℝ ∞
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T₀) α idx jdx))
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g r s
      (rawTensorConnLapSmooth (I := I) g r s T₀) α idx jdx
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_each_partial : ∀ k : Fin n,
      ContDiffOn ℝ ∞
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α idx jdx)))
        (chartTargetEuclid (I := I) (M := M) α) := fun k =>
    euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g r s T₀ α k idx jdx
  have h_each_partial2 : ∀ k l : Fin n,
      ContDiffOn ℝ ∞
        (euclidPartial (E := E) l
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α idx jdx))))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro k l
    set u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
      euclidPartial (E := E) k
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α idx jdx))
      with hu_def
    have hu := h_each_partial k
    have hsucc : ContDiffOn ℝ ((∞ : WithTop ℕ∞) + 1) u
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]; exact hu
    have hfw : ContDiffOn ℝ ∞ (fderivWithin ℝ u
        (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_succ_iff_fderivWithin h_open.uniqueDiffOn).mp hsucc).2.2
    have hfderiv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u z)
        (chartTargetEuclid (I := I) (M := M) α) := by
      refine hfw.congr (fun z hz => ?_)
      exact (fderivWithin_of_isOpen (f := u) (𝕜 := ℝ) h_open hz).symm
    have hcomp : ContDiffOn ℝ ∞
        ((fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
            L (EuclideanSpace.single l 1)) ∘ (fun z => fderiv ℝ u z))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single l 1)).contDiff.comp_contDiffOn hfderiv
    refine hcomp.congr (fun z _ => ?_)
    rfl
  set Coeff_LO_fn : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    fun y =>
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T₀) α idx jdx)) y -
      (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        weightedInvGramEuclid (I := I) (M := M) g α k l y *
          euclidPartial (E := E) l
            (euclidPartial (E := E) k
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s
                  T₀ α idx jdx))) y)
    with hCoeff_LO_fn_def
  have hCoeff_LO_fn_contDiffOn : ContDiffOn ℝ ∞ Coeff_LO_fn
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine ContDiffOn.sub h_chartPushed_raw_contDiffOn ?_
    refine ContDiffOn.sum (fun k _ => ContDiffOn.sum (fun l _ => ?_))
    exact (weightedInvGramEuclid_contDiffOn (I := I) (M := M) g α k l).mul
      (h_each_partial2 k l)
  obtain ⟨B_LO, hB_LO_nn, hB_LO_bd⟩ :=
    exists_sup_bound_of_contDiffOn_on_compact_subset
      hK_compact hK_sub hCoeff_LO_fn_contDiffOn
  refine ⟨2 * ((n : ℝ) ^ 2 * B_C ^ 2 + 1) * (1 + B_LO ^ 2), by positivity, ?_⟩
  intro b hb_inter
  obtain ⟨U, _hU_open, hb_U, _hU_good, _Coeff_2, _Coeff_LO,
    _hC2_cd, _hCLO_cd, hidentity⟩ :=
    tensorChartComponentRaw_rawTensorConnLap_eq_chart_α_coord_formula
      (I := I) g r s α T₀ idx jdx hb_inter
  have hLHS := hidentity b hb_U
  set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
  have hb_tsupp : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := hb_inter.1
  have hy_K : y ∈ K_set := ⟨b, hb_tsupp, rfl⟩
  let lhs : ℝ := tensorChartComponentRaw (I := I) (M := M) g r s
      (rawTensorConnLapSmooth (I := I) g r s T₀) α idx jdx b
  have hlhs_def : lhs = tensorChartComponentRaw (I := I) (M := M) g r s
      (rawTensorConnLapSmooth (I := I) g r s T₀) α idx jdx b := rfl
  have hlhs_eq_b : tensorChartComponentRaw (I := I) (M := M) g r s
      (rawTensorConnLapSmooth (I := I) g r s T₀) α idx jdx b = lhs := rfl
  have h_lhs_eq :
      lhs = (∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                weightedInvGramEuclid (I := I) (M := M) g α k l y *
                  euclidPartial (E := E) l
                    (euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M) g r s
                          T₀ α idx jdx))) y) +
              Coeff_LO_fn y := by
    have h_chartPushed_eq :
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T₀) α idx jdx)) y = lhs := by
      have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb_inter.2
      have hb_src : b ∈ (extChartAt I α).source :=
        chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb_good
      have hb_tgt : (extChartAt I α) b ∈ (extChartAt I α).target :=
        (extChartAt I α).map_source hb_src
      have hy_chartTarget : y ∈ chartTargetEuclid (I := I) (M := M) α :=
        ⟨(extChartAt I α) b, hb_tgt, rfl⟩
      rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_chartTarget]
      have hsymm_te : (toEuclidean (E := E)).symm
          ((toEuclidean (E := E)) ((extChartAt I α) b)) = (extChartAt I α) b :=
        (toEuclidean (E := E)).symm_apply_apply _
      have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
        (extChartAt I α).left_inv hb_src
      simp only [hy_def, hsymm_te, hleft_inv, hlhs_def]
    simp only [hCoeff_LO_fn_def, h_chartPushed_eq]
    ring
  set principal_sum : ℝ := ∑ k : Fin (Module.finrank ℝ E),
                            ∑ l : Fin (Module.finrank ℝ E),
                              weightedInvGramEuclid (I := I) (M := M) g α k l y *
                                euclidPartial (E := E) l
                                  (euclidPartial (E := E) k
                                    (chartPushedRaw I α
                                      (tensorChartComponentRaw
                                        (I := I) (M := M) g r s T₀ α idx jdx))) y
    with hps_def
  let SumPart2 : ℝ := ∑ k : Fin (Module.finrank ℝ E),
                  ∑ l : Fin (Module.finrank ℝ E),
                    (euclidPartial (E := E) l
                      (euclidPartial (E := E) k
                        (chartPushedRaw I α
                          (tensorChartComponentRaw
                            (I := I) (M := M) g r s T₀ α idx jdx)))
                      y) ^ 2
  have hSumPart2_def : SumPart2 = ∑ k : Fin (Module.finrank ℝ E),
                  ∑ l : Fin (Module.finrank ℝ E),
                    (euclidPartial (E := E) l
                      (euclidPartial (E := E) k
                        (chartPushedRaw I α
                          (tensorChartComponentRaw
                            (I := I) (M := M) g r s T₀ α idx jdx)))
                      y) ^ 2 := rfl
  have hSumPart2_nn : 0 ≤ SumPart2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have h_principal_sq : principal_sum ^ 2 ≤ (n : ℝ) ^ 2 * B_C ^ 2 * SumPart2 := by
    set Ckl : Fin n → Fin n → ℝ :=
      fun k l => weightedInvGramEuclid (I := I) (M := M) g α k l y with hCkl_def
    set Dkl : Fin n → Fin n → ℝ :=
      fun k l => euclidPartial (E := E) l
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α idx jdx))) y
      with hDkl_def
    have hps_eq : principal_sum = ∑ k : Fin n, ∑ l : Fin n, Ckl k l * Dkl k l :=
      rfl
    have h_cs : (∑ k : Fin n, ∑ l : Fin n, Ckl k l * Dkl k l) ^ 2 ≤
        (∑ k : Fin n, ∑ l : Fin n, Ckl k l ^ 2) *
          (∑ k : Fin n, ∑ l : Fin n, Dkl k l ^ 2) := by
      have h_prod_sum : ∀ (φ : Fin n × Fin n → ℝ),
          (∑ k : Fin n, ∑ l : Fin n, φ ⟨k, l⟩) =
            ∑ kl : Fin n × Fin n, φ kl := by
        intro φ
        rw [← Finset.sum_product']
        rfl
      have h1 := h_prod_sum (fun kl => Ckl kl.1 kl.2 * Dkl kl.1 kl.2)
      have h2 := h_prod_sum (fun kl => Ckl kl.1 kl.2 ^ 2)
      have h3 := h_prod_sum (fun kl => Dkl kl.1 kl.2 ^ 2)
      rw [h1, h2, h3]
      exact Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset (Fin n × Fin n))
        (fun kl => Ckl kl.1 kl.2) (fun kl => Dkl kl.1 kl.2)
    have h_C_sq_bd : (∑ k : Fin n, ∑ l : Fin n, Ckl k l ^ 2) ≤
        (n : ℝ) ^ 2 * B_C ^ 2 := by
      have h_each : ∀ k l : Fin n, Ckl k l ^ 2 ≤ B_C ^ 2 := by
        intro k l
        have h1 : |Ckl k l| ≤ B_C := hB_C_bd k l y hy_K
        have h2 : Ckl k l ^ 2 = |Ckl k l| ^ 2 := (sq_abs _).symm
        rw [h2]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      calc (∑ k : Fin n, ∑ l : Fin n, Ckl k l ^ 2)
          ≤ ∑ k : Fin n, ∑ l : Fin n, B_C ^ 2 :=
            Finset.sum_le_sum (fun k _ =>
              Finset.sum_le_sum (fun l _ => h_each k l))
        _ = (n : ℝ) ^ 2 * B_C ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            ring
    calc principal_sum ^ 2
        = (∑ k : Fin n, ∑ l : Fin n, Ckl k l * Dkl k l) ^ 2 := by rw [hps_eq]
      _ ≤ (∑ k : Fin n, ∑ l : Fin n, Ckl k l ^ 2) *
            (∑ k : Fin n, ∑ l : Fin n, Dkl k l ^ 2) := h_cs
      _ ≤ ((n : ℝ) ^ 2 * B_C ^ 2) *
            (∑ k : Fin n, ∑ l : Fin n, Dkl k l ^ 2) := by
            have hD_nn : 0 ≤ ∑ k : Fin n, ∑ l : Fin n, Dkl k l ^ 2 :=
              Finset.sum_nonneg (fun _ _ =>
                Finset.sum_nonneg (fun _ _ => sq_nonneg _))
            exact mul_le_mul_of_nonneg_right h_C_sq_bd hD_nn
      _ = (n : ℝ) ^ 2 * B_C ^ 2 * SumPart2 := by rfl
  have h_LO_abs : |Coeff_LO_fn y| ≤ B_LO := hB_LO_bd y hy_K
  have h_LO_sq : (Coeff_LO_fn y) ^ 2 ≤ B_LO ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg (Coeff_LO_fn y)) h_LO_abs 2
    rw [sq_abs] at this
    exact this
  have h_lhs_sq : lhs ^ 2 ≤ 2 * principal_sum ^ 2 + 2 * (Coeff_LO_fn y) ^ 2 := by
    rw [h_lhs_eq]
    nlinarith [sq_nonneg (principal_sum - Coeff_LO_fn y)]
  have h_final : lhs ^ 2 ≤
      2 * ((n : ℝ) ^ 2 * B_C ^ 2 + 1) * (1 + B_LO ^ 2) * (SumPart2 + 1) := by
    calc lhs ^ 2
        ≤ 2 * principal_sum ^ 2 + 2 * (Coeff_LO_fn y) ^ 2 := h_lhs_sq
      _ ≤ 2 * ((n : ℝ) ^ 2 * B_C ^ 2 * SumPart2) + 2 * B_LO ^ 2 := by
          gcongr
      _ ≤ 2 * ((n : ℝ) ^ 2 * B_C ^ 2 + 1) * (1 + B_LO ^ 2) * (SumPart2 + 1) := by
          have ha : 0 ≤ (n : ℝ) ^ 2 * B_C ^ 2 := by positivity
          have hb : 0 ≤ B_LO ^ 2 := sq_nonneg _
          nlinarith [hSumPart2_nn, ha, hb, mul_nonneg ha hSumPart2_nn,
            mul_nonneg hb hSumPart2_nn, mul_nonneg ha hb,
            mul_nonneg (mul_nonneg ha hb) hSumPart2_nn]
  rw [hlhs_eq_b, ← hSumPart2_def]
  exact h_final

end Connection
end Integral
end DifferentialGeometry

end
