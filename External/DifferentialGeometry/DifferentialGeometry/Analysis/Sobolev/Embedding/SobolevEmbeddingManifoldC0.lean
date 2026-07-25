import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.OffCentreFibreCore
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.LocalBallL2Embedding
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Topology Metric Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.PDE.RicciFlow.HebeyBlock
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem hsNorm_sq_toReal_eq
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) :
    (‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) k T‖) ^ 2 =
      ((tensorPouSobolevHsNorm (I := I) (M := M) g k T) ^ 2).toReal := by
  rw [tensorPouSobolevHilbert_norm_eq, ← ENNReal.toReal_pow]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem hsBlock_le_hsNorm_sq
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) (α₀ : M)
    (IJ₀ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))
    (j₀ : ℕ) (hj₀ : j₀ ∈ Finset.range (2 * k + 1)) :
    (∑ basisIdx : Fin j₀ → Fin (Module.finrank ℝ E),
        ∫⁻ y in chartTargetEuclid (I := I) (M := M) α₀,
          ENNReal.ofReal
            (((chartAtlasPOU I M α₀ : M → ℝ)
                ((extChartAt I α₀).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ j₀
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α₀
                        IJ₀.1 IJ₀.2
                      ∘ (extChartAt I α₀).symm
                      ∘ (toEuclidean (E := E)).symm)
                    y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
          ∂(volume : Measure EuclN))
      ≤ (tensorPouSobolevHsNorm (I := I) (M := M) g k T) ^ 2 := by
  classical
  set F : (α : M) → ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) → (j : ℕ) →
      (Fin j → Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun α IJ j basisIdx =>
      ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α
                      IJ.1 IJ.2
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        ∂(volume : Measure EuclN) with hF_def
  set S : ℝ≥0∞ :=
    ∑' α : M, ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * k + 1),
        ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E), F α IJ j basisIdx with hS_def
  have hnorm_sq :
      (tensorPouSobolevHsNorm (I := I) (M := M) g k T) ^ 2 = S := by
    have h_eq : tensorPouSobolevHsNorm (I := I) (M := M) g k T = S ^ (1 / 2 : ℝ) := by
      rw [tensorPouSobolevHsNorm_eq]
    rw [h_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  rw [hnorm_sq]
  set blk : ℝ≥0∞ :=
    ∑ basisIdx : Fin j₀ → Fin (Module.finrank ℝ E), F α₀ IJ₀ j₀ basisIdx with hblk
  have h_order :
      blk ≤ ∑ j ∈ Finset.range (2 * k + 1),
        ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E), F α₀ IJ₀ j basisIdx := by
    rw [hblk]
    exact Finset.single_le_sum
      (f := fun j => ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E), F α₀ IJ₀ j basisIdx)
      (fun j _ => zero_le _) hj₀
  have h_comp :
      (∑ j ∈ Finset.range (2 * k + 1),
        ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E), F α₀ IJ₀ j basisIdx) ≤
      ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * k + 1),
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E), F α₀ IJ j basisIdx :=
    Finset.single_le_sum
      (f := fun IJ => ∑ j ∈ Finset.range (2 * k + 1),
        ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E), F α₀ IJ j basisIdx)
      (fun IJ _ => zero_le _) (Finset.mem_univ IJ₀)
  have h_tsum :
      (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * k + 1),
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E), F α₀ IJ j basisIdx) ≤ S := by
    rw [hS_def]; exact ENNReal.le_tsum α₀
  exact le_trans h_order (le_trans h_comp h_tsum)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma euclN_coord_le_norm (v : EuclN) (i : Fin (Module.finrank ℝ E)) :
    |v i| ≤ ‖v‖ := by
  classical
  have h_sq : (v i) ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (f := fun j : Fin (Module.finrank ℝ E) => (v j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hv_norm_nn : 0 ≤ ‖v‖ := norm_nonneg _
  rw [show |v i| = Real.sqrt ((v i) ^ 2) from (Real.sqrt_sq_eq_abs _).symm,
    show ‖v‖ = Real.sqrt (‖v‖ ^ 2) from (Real.sqrt_sq hv_norm_nn).symm]
  exact Real.sqrt_le_sqrt h_sq

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem continuousMultilinearMap_norm_le_sum_abs_basis_apply
    {j : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => EuclN) ℝ) :
    ‖f‖ ≤ ∑ β : Fin j → Fin (Module.finrank ℝ E),
        |f (fun i => EuclideanSpace.single (β i) (1 : ℝ))| := by
  classical
  set Mb : ℝ := ∑ β : Fin j → Fin (Module.finrank ℝ E),
      |f (fun i => EuclideanSpace.single (β i) (1 : ℝ))| with hMb_def
  have hMb_nn : 0 ≤ Mb := Finset.sum_nonneg (fun β _ => abs_nonneg _)
  refine ContinuousMultilinearMap.opNorm_le_bound hMb_nn ?_
  intro m
  have h_expand : ∀ i : Fin j, m i =
      ∑ a : Fin (Module.finrank ℝ E), (m i a) • EuclideanSpace.single a (1 : ℝ) := by
    intro i
    have h := (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).sum_repr (m i)
    rw [show (fun a : Fin (Module.finrank ℝ E) => (m i a) • EuclideanSpace.single a (1 : ℝ)) =
      (fun a : Fin (Module.finrank ℝ E) =>
        (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).repr (m i) a •
          (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ) a) from ?_, h]
    funext a
    rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have h_f_expand :
      f m = ∑ β : Fin j → Fin (Module.finrank ℝ E),
        (∏ i : Fin j, m i (β i)) *
          f (fun i => EuclideanSpace.single (β i) (1 : ℝ)) := by
    have h_step1 : f m = f (fun i : Fin j =>
        ∑ a : Fin (Module.finrank ℝ E), (m i a) • EuclideanSpace.single a (1 : ℝ)) := by
      congr; funext i; exact h_expand i
    rw [h_step1]
    have h_mult_sum :
        (f.toMultilinearMap fun i : Fin j =>
          ∑ a : Fin (Module.finrank ℝ E), (m i a) • EuclideanSpace.single a (1 : ℝ)) =
        ∑ β : Fin j → Fin (Module.finrank ℝ E),
          f.toMultilinearMap fun i : Fin j =>
            (m i (β i)) • EuclideanSpace.single (β i) (1 : ℝ) :=
      f.toMultilinearMap.map_sum
        (fun (i : Fin j) (a : Fin (Module.finrank ℝ E)) =>
          (m i a) • EuclideanSpace.single a (1 : ℝ))
    change f.toMultilinearMap _ = _
    rw [h_mult_sum]
    refine Finset.sum_congr rfl ?_
    intro β _
    rw [f.toMultilinearMap.map_smul_univ
      (c := fun i : Fin j => m i (β i))
      (m := fun i : Fin j => EuclideanSpace.single (β i) (1 : ℝ))]
    rw [smul_eq_mul]; rfl
  rw [Real.norm_eq_abs, h_f_expand]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h_inner_bound : ∀ β : Fin j → Fin (Module.finrank ℝ E),
      |(∏ i : Fin j, m i (β i)) *
          f (fun i => EuclideanSpace.single (β i) (1 : ℝ))| ≤
        (∏ i : Fin j, ‖m i‖) *
          |f (fun i => EuclideanSpace.single (β i) (1 : ℝ))| := by
    intro β
    rw [abs_mul]
    have h_prod_le : |∏ i : Fin j, m i (β i)| ≤ ∏ i : Fin j, ‖m i‖ := by
      rw [Finset.abs_prod]
      refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => euclN_coord_le_norm (m i) (β i))
    exact mul_le_mul_of_nonneg_right h_prod_le (abs_nonneg _)
  refine (Finset.sum_le_sum (fun β _ => h_inner_bound β)).trans ?_
  have h_factor :
      ∑ β : Fin j → Fin (Module.finrank ℝ E),
        (∏ i : Fin j, ‖m i‖) *
          |f (fun i => EuclideanSpace.single (β i) (1 : ℝ))| =
      (∏ i : Fin j, ‖m i‖) * Mb := by rw [← Finset.mul_sum]
  rw [h_factor]; exact le_of_eq (mul_comm _ _)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem continuousMultilinearMap_norm_sq_le_finrank_pow_mul_sum_basisFun_sq
    {j : ℕ}
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin j => EuclN) ℝ) :
    ‖f‖ ^ 2 ≤
      ((Module.finrank ℝ E) ^ j : ℕ) *
        ∑ β : Fin j → Fin (Module.finrank ℝ E),
          |f (fun i => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ (β i))| ^ 2 := by
  classical
  simp only [EuclideanSpace.basisFun_apply]
  have h1 := continuousMultilinearMap_norm_le_sum_abs_basis_apply (E := E) f
  have h1' : ‖f‖ ^ 2 ≤
      (∑ β : Fin j → Fin (Module.finrank ℝ E),
        |f (fun i => EuclideanSpace.single (β i) (1 : ℝ))|) ^ 2 := by
    have hf_nn : 0 ≤ ‖f‖ := norm_nonneg _
    nlinarith [h1, hf_nn, Finset.sum_nonneg
      (fun (β : Fin j → Fin (Module.finrank ℝ E)) (_ : β ∈ Finset.univ) => abs_nonneg
        (f (fun i => EuclideanSpace.single (β i) (1 : ℝ))))]
  refine h1'.trans ?_
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin j → Fin (Module.finrank ℝ E))))
    (f := fun β => |f (fun i => EuclideanSpace.single (β i) (1 : ℝ))|)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hcs
  exact hcs

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem rawPull_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_raw_smoothOn : ContMDiffOn I (𝓘(ℝ, ℝ)) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)
      ((chartAt H α).source) :=
    tensorChartComponentRaw_contMDiffOn_chart_source (I := I) (M := M) g r s T α Idx Jdx
  have h_raw_pull_contDiffOn :
      ContDiffOn ℝ ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm)
        (extChartAt I α).target := by
    have h_extSymm : ContMDiffOn 𝓘(ℝ, E) I ∞
        ((extChartAt I α).symm : E → M) (extChartAt I α).target :=
      contMDiffOn_extChartAt_symm α
    have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, ℝ)) ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm)
        (extChartAt I α).target := by
      refine h_raw_smoothOn.comp h_extSymm ?_
      intro y hy
      change (extChartAt I α).symm y ∈ (chartAt H α).source
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I α).map_target hy
    exact h_comp_mdiff.contDiffOn
  have h_toEucl_symm_smooth : ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
    ContinuousLinearEquiv.contDiff _
  have h_maps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α)
      (extChartAt I α).target := by
    intro y hy
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm
      (I := I) (M := M)] at hy
    exact hy
  exact h_raw_pull_contDiffOn.comp h_toEucl_symm_smooth.contDiffOn h_maps

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem exists_global_smooth_eqOn_ball_of_rawPull
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y₀ : EuclN} {R : ℝ}
    (hball : Metric.closedBall y₀ R ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ∃ ftil : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ftil ∧
      Set.EqOn ftil
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm)
        (Metric.closedBall y₀ R) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  set rp : EuclN → ℝ :=
    tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
      ∘ (extChartAt I α).symm
      ∘ (toEuclidean (E := E)).symm with hrp_def
  have hrp_on : ContDiffOn ℝ ∞ rp Ω :=
    rawPull_contDiffOn (I := I) (M := M) g r s T α Idx Jdx
  obtain ⟨δ, η, hδ_pos, _hδ_sub, hη_smooth, hη_cpt, _hη_range, hη_one, hη_supp⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E)
      (isCompact_closedBall y₀ R) hΩ_open hball
  refine ⟨fun y => η y * rp y, ?_, ?_⟩
  · have hη_smooth' : ContDiff ℝ ∞ η := hη_smooth
    have h_on_Ω : ContDiffOn ℝ ∞ (fun y => η y * rp y) Ω :=
      hη_smooth'.contDiffOn.mul hrp_on
    set t : Set EuclN := (tsupport η)ᶜ with ht_def
    have ht_open : IsOpen t := (isClosed_tsupport η).isOpen_compl
    have h_on_t : ContDiffOn ℝ ∞ (fun y => η y * rp y) t := by
      refine (contDiffOn_congr (f := fun _ : EuclN => (0 : ℝ)) ?_).mpr contDiffOn_const
      intro y hy
      have hη0 : η y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hη0]
    have h_union : Ω ∪ t = Set.univ := by
      rw [hΩ_def, ht_def, Set.union_comm, Set.eq_univ_iff_forall]
      intro y
      by_cases hy : y ∈ tsupport η
      · exact Or.inr (hη_supp hy)
      · exact Or.inl hy
    exact contDiff_of_contDiffOn_union_of_isOpen h_on_Ω h_on_t h_union hΩ_open ht_open
  · intro y hy
    have hη_y : η y = 1 := hη_one y (Metric.self_subset_cthickening _ hy)
    simp only [hη_y, one_mul, hrp_def]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private theorem hsIntegrandReal_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun z : EuclN =>
        ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) *
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm)
                z)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α
  have hPOU_pull_cont :
      ContinuousOn (fun z : EuclN =>
          (chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)))
        (chartTargetEuclid (I := I) (M := M) α) := by
    have hPOU_cont : Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous
    exact hPOU_cont.comp_continuousOn'
      (DifferentialGeometry.Analysis.Sobolev.Chart.continuousOn_symm_toEuclideanSymm
        (I := I) (M := M) α)
  have h_cdOn := rawPull_contDiffOn (I := I) (M := M) g r s T α IJ.1 IJ.2
  have h_iter_contOn : ContinuousOn
      (fun z => iteratedFDeriv ℝ j
        (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) z)
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro z hz
    have h_cd : ContDiffAt ℝ ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) z :=
      h_cdOn.contDiffAt (h_open.mem_nhds hz)
    exact (h_cd.continuousAt_iteratedFDeriv (k := j)
      (by exact_mod_cast le_top)).continuousWithinAt
  have h_eval_contOn : ContinuousOn
      (fun z : EuclN =>
        (iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm) z)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_apply : Continuous
        (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin j => EuclN) ℝ =>
          A (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))) :=
      continuous_eval_const _
    exact h_apply.comp_continuousOn h_iter_contOn
  exact hPOU_pull_cont.mul ((h_eval_contOn.abs).pow 2)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem eLpNorm_sq_iteratedFDeriv_le_hsBlock
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)))
    (j : ℕ) {y₀ : EuclN} {R c : ℝ} (hc_pos : 0 < c)
    (hball_sub : Metric.ball y₀ R ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hρ_lb : ∀ y ∈ Metric.ball y₀ R,
      c ≤ (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) :
    (eLpNorm (fun z => ‖iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
            ∘ (extChartAt I α).symm
            ∘ (toEuclidean (E := E)).symm) z‖) 2
        ((volume : Measure EuclN).restrict (Metric.ball y₀ R))) ^ 2
      ≤ ENNReal.ofReal (((Module.finrank ℝ E) ^ j : ℕ) * c⁻¹) *
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T α
                            IJ.1 IJ.2
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
              ∂(volume : Measure EuclN) := by
  classical
  set f : EuclN → ℝ :=
    tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
      ∘ (extChartAt I α).symm
      ∘ (toEuclidean (E := E)).symm with hf_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_meas : MeasurableSet Ω :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  have hball_meas : MeasurableSet (Metric.ball y₀ R) := measurableSet_ball
  set cardj : ℝ := (((Module.finrank ℝ E) ^ j : ℕ) : ℝ) with hcardj_def
  have hcardj_nn : 0 ≤ cardj := by positivity
  have h_eLp_sq :
      (eLpNorm (fun z => ‖iteratedFDeriv ℝ j f z‖) 2
          ((volume : Measure EuclN).restrict (Metric.ball y₀ R))) ^ 2 =
        ∫⁻ z in Metric.ball y₀ R, ‖(‖iteratedFDeriv ℝ j f z‖)‖ₑ ^ 2 ∂(volume : Measure EuclN) := by
    have h := eLpNorm_nnreal_pow_eq_lintegral
      (μ := (volume : Measure EuclN).restrict (Metric.ball y₀ R))
      (f := fun z => ‖iteratedFDeriv ℝ j f z‖) (p := (2 : ℝ≥0)) (by norm_num)
    rw [show ((2 : ℝ≥0) : ℝ≥0∞) = (2 : ℝ≥0∞) by norm_num] at h
    rw [show ((2 : ℝ≥0) : ℝ) = ((2 : ℕ) : ℝ) by norm_num] at h
    rw [ENNReal.rpow_natCast] at h
    simp only [ENNReal.rpow_natCast] at h
    exact h
  rw [h_eLp_sq]
  have h_int_le :
      (∫⁻ z in Metric.ball y₀ R, ‖(‖iteratedFDeriv ℝ j f z‖)‖ₑ ^ 2 ∂(volume : Measure EuclN))
        ≤ ∫⁻ z in Metric.ball y₀ R,
            ENNReal.ofReal cardj *
              (ENNReal.ofReal c⁻¹ *
                ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) *
                      |(iteratedFDeriv ℝ j f z)
                          (fun i => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)) ∂(volume : Measure EuclN) := by
    refine lintegral_mono_ae ?_
    refine (ae_restrict_iff' hball_meas).2 ?_
    filter_upwards with z hz
    have hLHS : ‖(‖iteratedFDeriv ℝ j f z‖)‖ₑ ^ 2 =
        ENNReal.ofReal (‖iteratedFDeriv ℝ j f z‖ ^ 2) := by
      rw [Real.enorm_eq_ofReal (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [hLHS]
    have hρz : c ≤ (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := hρ_lb z hz
    have hρz_pos : 0 < (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := lt_of_lt_of_le hc_pos hρz
    have h_hs := continuousMultilinearMap_norm_sq_le_finrank_pow_mul_sum_basisFun_sq (E := E)
      (iteratedFDeriv ℝ j f z)
    have h_weight :
        (∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            |(iteratedFDeriv ℝ j f z)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
          ≤ c⁻¹ * ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) *
                |(iteratedFDeriv ℝ j f z)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun b _ => ?_)
      have h_one_le : (1 : ℝ) ≤ c⁻¹ *
          (chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := by
        rw [inv_mul_eq_div, le_div_iff₀ hc_pos, one_mul]; exact hρz
      have hsq_nn : (0 : ℝ) ≤ |(iteratedFDeriv ℝ j f z)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (b i))| ^ 2 := by positivity
      calc |(iteratedFDeriv ℝ j f z)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (b i))| ^ 2
          = 1 * |(iteratedFDeriv ℝ j f z)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (b i))| ^ 2 := by ring
        _ ≤ (c⁻¹ * (chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) *
            |(iteratedFDeriv ℝ j f z)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (b i))| ^ 2 :=
            mul_le_mul_of_nonneg_right h_one_le hsq_nn
        _ = c⁻¹ * ((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) *
            |(iteratedFDeriv ℝ j f z)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (b i))| ^ 2) := by ring
    have h_real : ‖iteratedFDeriv ℝ j f z‖ ^ 2 ≤
        cardj *
          (c⁻¹ *
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) *
                |(iteratedFDeriv ℝ j f z)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) := by
      refine h_hs.trans ?_
      rw [hcardj_def]
      exact mul_le_mul_of_nonneg_left h_weight (by positivity)
    have h_sum_eq :
        (∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) *
                |(iteratedFDeriv ℝ j f z)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)) =
          ENNReal.ofReal (∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))) *
                |(iteratedFDeriv ℝ j f z)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro b _
      exact mul_nonneg (le_of_lt hρz_pos) (by positivity)
    rw [h_sum_eq, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hcardj_nn]
    exact ENNReal.ofReal_le_ofReal h_real
  refine h_int_le.trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [ENNReal.ofReal_mul hcardj_nn, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  refine mul_le_mul_of_nonneg_left ?_ (zero_le _)
  rw [lintegral_finset_sum']
  swap
  · intro b _
    refine ContinuousOn.aemeasurable ?_ hball_meas
    refine ENNReal.continuous_ofReal.comp_continuousOn ?_
    exact (hsIntegrandReal_continuousOn (I := I) (M := M) g r s T α IJ j b).mono hball_sub
  refine Finset.sum_le_sum (fun b _ => ?_)
  exact lintegral_mono_set hball_sub

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem smooth_eLpNorm_iteratedFDeriv_ball_ne_top
    {y₀ : EuclN} {R : ℝ} (j : ℕ) {u : EuclN → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    eLpNorm (fun z => ‖iteratedFDeriv ℝ j u z‖) 2
      ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) ≠ ⊤ := by
  have h_iter_cont : Continuous (fun z : EuclN => iteratedFDeriv ℝ j u z) := by
    have h := hu.iteratedFDeriv_right' (m := (⊤ : ℕ∞)) (i := j)
    simpa using h.continuous
  have hcont : Continuous (fun z : EuclN => ‖iteratedFDeriv ℝ j u z‖) :=
    continuous_norm.comp h_iter_cont
  obtain ⟨Mb, hMb⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_closedBall y₀ R) hcont.continuousOn
  haveI : IsFiniteMeasure ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top
  refine MemLp.eLpNorm_ne_top ?_
  refine MemLp.of_le_mul (g := fun _ : EuclN => (1 : ℝ)) (c := Mb) ?_ ?_ ?_
  · exact memLp_const (1 : ℝ)
  · exact hcont.aestronglyMeasurable.restrict
  · refine (ae_restrict_iff' measurableSet_ball).mpr ?_
    filter_upwards with z hz
    have hz' : z ∈ Metric.closedBall y₀ R := Metric.ball_subset_closedBall hz
    rw [norm_one, mul_one]
    exact hMb z hz'

omit [BoundarylessManifold I M] in
private theorem rawPullCenter_le_hsNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)
    (hk : (Module.finrank ℝ E : ℝ) < 2 * (2 * k))
    (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)))
    {y₀ : EuclN} {R c : ℝ} (hR : 0 < R) (hc_pos : 0 < c)
    (hball : Metric.closedBall y₀ R ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hρ_lb : ∀ y ∈ Metric.ball y₀ R,
      c ≤ (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) :
    ∃ Cα : ℝ, 0 ≤ Cα ∧ ∀ (T' : SmoothCcTensor g r s),
      ∀ y₁ ∈ Metric.ball y₀ (R / 4),
      |tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y₁))|
        ≤ Cα * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T'‖ := by
  classical
  have hk' : (Module.finrank ℝ E : ℝ) < 2 * ((2 * k : ℕ) : ℝ) := by push_cast; linarith [hk]
  obtain ⟨Cloc, hCloc_nn, hCloc⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.smooth_localBall_L2_pointwise_embedding
      (d := Module.finrank ℝ E) (K := 2 * k) hk' (x₀ := y₀) (R := R) hR
  set A : ℝ := Real.sqrt (((Module.finrank ℝ E) ^ (2 * (2 * k)) : ℕ) * c⁻¹) with hA_def
  have hA_nn : 0 ≤ A := Real.sqrt_nonneg _
  refine ⟨Cloc * ((2 * (2 * k) + 1 : ℕ) * A), by positivity, ?_⟩
  intro T' y₁ hy₁
  set hsn : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T'‖ with hhsn_def
  have hhsn_nn : 0 ≤ hsn := norm_nonneg _
  obtain ⟨ftil, hftil_smooth, hftil_eq⟩ :=
    exists_global_smooth_eqOn_ball_of_rawPull (I := I) (M := M) g r s T' α IJ.1 IJ.2 hball
  have hy₁_cb : y₁ ∈ Metric.closedBall y₀ R :=
    (Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall hy₁
  have h_loc := hCloc (f := ftil) hftil_smooth y₁ hy₁
  have hftil_y0 : ftil y₁ =
      tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y₁)) := by
    have := hftil_eq hy₁_cb
    simpa [Function.comp_apply] using this
  have hball_open : Metric.ball y₀ R ⊆ chartTargetEuclid (I := I) (M := M) α :=
    (Metric.ball_subset_closedBall).trans hball
  have h_eqOn_ball : Set.EqOn ftil
      (tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) (Metric.ball y₀ R) :=
    hftil_eq.mono Metric.ball_subset_closedBall
  have h_eLp_eq : ∀ j,
      eLpNorm (fun z => ‖iteratedFDeriv ℝ j ftil z‖) 2
          ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) =
        eLpNorm (fun z => ‖iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm) z‖) 2
          ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) := by
    intro j
    refine eLpNorm_congr_ae ?_
    refine (ae_restrict_iff' measurableSet_ball).2 (Filter.Eventually.of_forall (fun z hz => ?_))
    have hball_nhd : Metric.ball y₀ R ∈ nhds z := Metric.isOpen_ball.mem_nhds hz
    have h_ev : ftil =ᶠ[nhds z]
        (tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) :=
      Filter.eventuallyEq_of_mem hball_nhd h_eqOn_ball
    have h_iter_eq := (h_ev.iteratedFDeriv ℝ j).eq_of_nhds
    simp only [h_iter_eq]
  have h_per_order : ∀ j ∈ Finset.range (2 * (2 * k) + 1),
      (eLpNorm (fun z => ‖iteratedFDeriv ℝ j ftil z‖) 2
        ((volume : Measure EuclN).restrict (Metric.ball y₀ R))).toReal ≤ A * hsn := by
    intro j hj
    rw [h_eLp_eq j]
    set X : ℝ≥0∞ := eLpNorm (fun z => ‖iteratedFDeriv ℝ j
        (tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) z‖) 2
      ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) with hX_def
    have hX_ne_top : X ≠ ⊤ := by
      rw [hX_def, ← h_eLp_eq j]
      exact smooth_eLpNorm_iteratedFDeriv_ball_ne_top (j := j) hftil_smooth
    have h_key := eLpNorm_sq_iteratedFDeriv_le_hsBlock (I := I) (M := M)
      g r s T' α IJ j hc_pos hball_open hρ_lb
    rw [← hX_def] at h_key
    have h_blk_le := hsBlock_le_hsNorm_sq (I := I) (M := M) g (2 * k) T' α IJ j hj
    have hcard_nn : (0 : ℝ) ≤ ((Module.finrank ℝ E) ^ (2 * (2 * k)) : ℕ) := by positivity
    have h_X_sq_le :
        X ^ 2 ≤ ENNReal.ofReal (((Module.finrank ℝ E) ^ j : ℕ) * c⁻¹) *
          (tensorPouSobolevHsNorm (I := I) (M := M) g (2 * k) T') ^ 2 :=
      h_key.trans (mul_le_mul_of_nonneg_left h_blk_le (zero_le _))
    have h_hsn_ne_top : (tensorPouSobolevHsNorm (I := I) (M := M) g (2 * k) T') ≠ ⊤ :=
      (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g (2 * k) T').ne
    have h_rhs_ne_top :
        ENNReal.ofReal (((Module.finrank ℝ E) ^ j : ℕ) * c⁻¹) *
          (tensorPouSobolevHsNorm (I := I) (M := M) g (2 * k) T') ^ 2 ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_ne_top h_hsn_ne_top)
    have h_toReal := ENNReal.toReal_mono h_rhs_ne_top h_X_sq_le
    rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (by positivity), ENNReal.toReal_pow] at h_toReal
    have h_hsn_eq : (tensorPouSobolevHsNorm (I := I) (M := M) g (2 * k) T').toReal = hsn := by
      rw [hhsn_def, tensorPouSobolevHilbert_norm_eq]
    rw [h_hsn_eq] at h_toReal
    have hX_toReal_nn : 0 ≤ X.toReal := ENNReal.toReal_nonneg
    have h_card_mono : (((Module.finrank ℝ E) ^ j : ℕ) : ℝ) * c⁻¹ ≤ A ^ 2 := by
      rw [hA_def, Real.sq_sqrt (by positivity)]
      have hjle : j ≤ 2 * (2 * k) := by rw [Finset.mem_range] at hj; omega
      have : ((Module.finrank ℝ E) ^ j : ℕ) ≤ ((Module.finrank ℝ E) ^ (2 * (2 * k)) : ℕ) :=
        Nat.pow_le_pow_right (NeZero.pos _) hjle
      have hcast : (((Module.finrank ℝ E) ^ j : ℕ) : ℝ) ≤
          (((Module.finrank ℝ E) ^ (2 * (2 * k)) : ℕ) : ℝ) := by exact_mod_cast this
      exact mul_le_mul_of_nonneg_right hcast (by positivity)
    have h_Xsq_le_Asq : X.toReal ^ 2 ≤ (A * hsn) ^ 2 := by
      refine h_toReal.trans ?_
      have hhsn_sq_nn : 0 ≤ hsn ^ 2 := by positivity
      calc (((Module.finrank ℝ E) ^ j : ℕ) : ℝ) * c⁻¹ * hsn ^ 2
          ≤ A ^ 2 * hsn ^ 2 := mul_le_mul_of_nonneg_right h_card_mono hhsn_sq_nn
        _ = (A * hsn) ^ 2 := by ring
    have hAhsn_nn : 0 ≤ A * hsn := mul_nonneg hA_nn hhsn_nn
    calc X.toReal = Real.sqrt (X.toReal ^ 2) := (Real.sqrt_sq hX_toReal_nn).symm
      _ ≤ Real.sqrt ((A * hsn) ^ 2) := Real.sqrt_le_sqrt h_Xsq_le_Asq
      _ = A * hsn := Real.sqrt_sq hAhsn_nn
  rw [← hftil_y0, ← Real.norm_eq_abs]
  refine h_loc.trans ?_
  have h_sum_le :
      (∑ j ∈ Finset.range (2 * (2 * k) + 1),
          (eLpNorm (fun z => ‖iteratedFDeriv ℝ j ftil z‖) 2
            ((volume : Measure EuclN).restrict (Metric.ball y₀ R))).toReal)
        ≤ ((2 * (2 * k) + 1 : ℕ) : ℝ) * (A * hsn) := by
    have h_each := Finset.sum_le_sum h_per_order
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h_each
    exact h_each
  calc Cloc * (∑ j ∈ Finset.range (2 * (2 * k) + 1),
          (eLpNorm (fun z => ‖iteratedFDeriv ℝ j ftil z‖) 2
            ((volume : Measure EuclN).restrict (Metric.ball y₀ R))).toReal)
      ≤ Cloc * (((2 * (2 * k) + 1 : ℕ) : ℝ) * (A * hsn)) :=
        mul_le_mul_of_nonneg_left h_sum_le hCloc_nn
    _ = Cloc * (((2 * (2 * k) + 1 : ℕ) : ℝ) * A) * hsn := by ring

omit [BoundarylessManifold I M] in
private theorem uniformRawPull_le_hsNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)
    (hk : (Module.finrank ℝ E : ℝ) < 2 * (2 * k))
    (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)))
    {Kc O : Set EuclN} {c : ℝ} (hc_pos : 0 < c)
    (hKc_compact : IsCompact Kc) (hO_open : IsOpen O)
    (hKcO : Kc ⊆ O) (hO_sub : O ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hρ_lb : ∀ y ∈ O,
      c ≤ (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T' : SmoothCcTensor g r s), ∀ y ∈ Kc,
      |tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))|
        ≤ D * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T'‖ := by
  classical
  rcases Set.eq_empty_or_nonempty Kc with hKc_empty | hKc_ne
  · exact ⟨0, le_refl 0, fun T' y hy => by rw [hKc_empty] at hy; exact absurd hy (Set.notMem_empty y)⟩
  obtain ⟨δ, hδ_pos, hδ_ball⟩ :=
    lebesgue_number_lemma_of_metric (s := Kc) (c := fun _ : Unit => O)
      hKc_compact (fun _ => hO_open) (by intro x hx; exact Set.mem_iUnion.mpr ⟨(), hKcO hx⟩)
  have hδ_sub : ∀ y ∈ Kc, Metric.ball y δ ⊆ O := by
    intro y hy
    obtain ⟨_, hsub⟩ := hδ_ball y hy
    exact hsub
  have hδ2_pos : 0 < δ / 2 := by linarith
  have h_center : ∀ y : Kc, ∃ Cy : ℝ, 0 ≤ Cy ∧ ∀ (T' : SmoothCcTensor g r s),
      ∀ y₁ ∈ Metric.ball (y : EuclN) ((δ / 2) / 4),
      |tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y₁))|
        ≤ Cy * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T'‖ := by
    intro y
    have hhalf_lt : δ / 2 < δ := half_lt_self hδ_pos
    have hhalf_le : δ / 2 ≤ δ := le_of_lt hhalf_lt
    have hcb_sub : Metric.closedBall (y : EuclN) (δ / 2) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
      refine (Metric.closedBall_subset_ball hhalf_lt).trans ?_
      exact (hδ_sub y y.2).trans hO_sub
    have hρ_ball : ∀ z ∈ Metric.ball (y : EuclN) (δ / 2),
        c ≤ (chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) := by
      intro z hz
      have hz' : z ∈ Metric.ball (y : EuclN) δ :=
        Metric.ball_subset_ball hhalf_le hz
      exact hρ_lb z (hδ_sub y y.2 hz')
    obtain ⟨Cy, hCy_nn, hCy⟩ :=
      rawPullCenter_le_hsNorm (I := I) (M := M) g r s k hk
        α IJ hδ2_pos hc_pos hcb_sub hρ_ball
    exact ⟨Cy, hCy_nn, hCy⟩
  choose Cfun hCfun_nn hCfun using h_center
  obtain ⟨tcov, htcov⟩ :=
    hKc_compact.elim_finite_subcover
      (U := fun y : Kc => Metric.ball (y : EuclN) ((δ / 2) / 4))
      (fun y => Metric.isOpen_ball)
      (by
        intro z hz
        refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
        rw [Metric.mem_ball, dist_self]; positivity)
  set Dmax : ℝ := (tcov.image Cfun).sup' (by
    rcases hKc_ne with ⟨z, hz⟩
    obtain ⟨y, hy_t, _⟩ := Set.mem_iUnion₂.mp (htcov hz)
    exact Finset.image_nonempty.mpr ⟨y, hy_t⟩) id ⊔ 0 with hDmax_def
  have hDmax_nn : 0 ≤ Dmax := le_sup_right
  refine ⟨Dmax, hDmax_nn, ?_⟩
  intro T' y hy
  set hsn : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T'‖ with hhsn_def
  have hhsn_nn : 0 ≤ hsn := norm_nonneg _
  obtain ⟨yi, hyi_t, hy_in⟩ := Set.mem_iUnion₂.mp (htcov hy)
  have h_bound := hCfun yi T' y hy_in
  have hCyi_le : Cfun yi ≤ Dmax := by
    rw [hDmax_def]
    refine le_sup_of_le_left ?_
    exact Finset.le_sup' id (Finset.mem_image_of_mem Cfun hyi_t)
  calc |tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))|
      ≤ Cfun yi * hsn := h_bound
    _ ≤ Dmax * hsn := mul_le_mul_of_nonneg_right hCyi_le hhsn_nn

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem superlevel_compact_subset_source
    (α : M) {c : ℝ} (hc_pos : 0 < c) :
    IsCompact {x : M | c ≤ (chartAtlasPOU I M α : M → ℝ) x} ∧
      {x : M | c ≤ (chartAtlasPOU I M α : M → ℝ) x} ⊆ (chartAt H α).source := by
  classical
  have hρ_cont : Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous
  have hclosed : IsClosed {x : M | c ≤ (chartAtlasPOU I M α : M → ℝ) x} :=
    isClosed_le continuous_const hρ_cont
  refine ⟨hclosed.isCompact, ?_⟩
  intro x hx
  have hx_pos : (0 : ℝ) < (chartAtlasPOU I M α : M → ℝ) x := lt_of_lt_of_le hc_pos hx
  have hx_supp : x ∈ Function.support (fun y : M => (chartAtlasPOU I M α : M → ℝ) y) :=
    ne_of_gt hx_pos
  have hx_tsupp : x ∈ tsupport (fun y : M => (chartAtlasPOU I M α : M → ℝ) y) :=
    subset_tsupport _ hx_supp
  exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α hx_tsupp

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
private theorem chartFiberNorm_le_hsNorm_on_superlevel
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)
    (hk : (Module.finrank ℝ E : ℝ) < 2 * (2 * k))
    (α : M) {c : ℝ} (hc_pos : 0 < c) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : SmoothCcTensor g r s),
      ∀ x ∈ {x : M | c ≤ (chartAtlasPOU I M α : M → ℝ) x},
        ‖T.toSection x‖ ≤ D *
          ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  classical
  set Kset : Set M := {x : M | c ≤ (chartAtlasPOU I M α : M → ℝ) x} with hKset_def
  obtain ⟨hK_compact, hK_sub⟩ := superlevel_compact_subset_source (I := I) (M := M) α hc_pos
  rw [← hKset_def] at hK_compact hK_sub
  obtain ⟨C₁, hC₁_pos, hC₁⟩ :=
    tensorFiberNorm_sq_le_chartAlphaComponents_on_compact (I := I) (M := M) g r s α
      hK_compact hK_sub
  set Kc : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' Kset) with hKc_def
  have hKc_compact : IsCompact Kc := by
    have h1 : IsCompact ((extChartAt I α) '' Kset) :=
      hK_compact.image_of_continuousOn
        ((continuousOn_extChartAt α).mono (by
          intro x hx; rw [extChartAt_source]; exact hK_sub hx))
    exact h1.image (toEuclidean (E := E)).continuous
  set O : Set EuclN :=
    chartTargetEuclid (I := I) (M := M) α ∩
      (fun y : EuclN => (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ⁻¹' (Set.Ioi (c / 2))
    with hO_def
  have hO_open : IsOpen O := by
    rw [hO_def]
    have hρ_cont : Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous
    have hcontOn : ContinuousOn
        (fun y : EuclN => (chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      hρ_cont.comp_continuousOn'
        (DifferentialGeometry.Analysis.Sobolev.Chart.continuousOn_symm_toEuclideanSymm
          (I := I) (M := M) α)
    exact hcontOn.isOpen_inter_preimage
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen (I := I) (M := M) α)
      isOpen_Ioi
  have hO_sub : O ⊆ chartTargetEuclid (I := I) (M := M) α := by
    rw [hO_def]; exact Set.inter_subset_left
  have hx_ext_src : ∀ x ∈ Kset, x ∈ (extChartAt I α).source := by
    intro x hx; rw [extChartAt_source]; exact hK_sub hx
  have hpull_eq : ∀ x ∈ Kset,
      (extChartAt I α).symm ((toEuclidean (E := E)).symm
        ((toEuclidean (E := E)) ((extChartAt I α) x))) = x := by
    intro x hx
    rw [(toEuclidean (E := E)).symm_apply_apply]
    exact (extChartAt I α).left_inv (hx_ext_src x hx)
  have hKcO : Kc ⊆ O := by
    intro y hy
    rw [hKc_def] at hy
    obtain ⟨z, ⟨x, hx_K, hxz⟩, hzy⟩ := hy
    have hy_eq : y = (toEuclidean (E := E)) ((extChartAt I α) x) := by rw [hxz]; exact hzy.symm
    have hpull : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = x := by
      rw [hy_eq]; exact hpull_eq x hx_K
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := by
      rw [hy_eq]
      exact ⟨(extChartAt I α) x, (extChartAt I α).map_source (hx_ext_src x hx_K), rfl⟩
    refine ⟨hy_target, ?_⟩
    have hgoal : c / 2 < (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
      rw [hpull]
      have hx_ge : c ≤ (chartAtlasPOU I M α : M → ℝ) x := hx_K
      linarith [hc_pos, hx_ge]
    exact hgoal
  have hρ_on_O : ∀ y ∈ O,
      c / 2 ≤ (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
    intro y hy
    rw [hO_def] at hy
    exact le_of_lt hy.2
  have hc2_pos : 0 < c / 2 := by linarith
  have h_comp : ∀ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)),
      ∃ Dij : ℝ, 0 ≤ Dij ∧ ∀ (T' : SmoothCcTensor g r s), ∀ y ∈ Kc,
        |tensorChartComponentRaw (I := I) (M := M) g r s T' α IJ.1 IJ.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))|
          ≤ Dij * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T'‖ := by
    intro IJ
    exact uniformRawPull_le_hsNorm (I := I) (M := M) g r s k hk α IJ hc2_pos
      hKc_compact hO_open hKcO hO_sub hρ_on_O
  choose Dfun hDfun_nn hDfun using h_comp
  set Dmax : ℝ := (Finset.univ.sup' (Finset.univ_nonempty) Dfun) ⊔ 0 with hDmax_def
  have hDmax_nn : 0 ≤ Dmax := le_sup_right
  set npairs : ℝ := (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) : ℝ) with hnp_def
  have hnp_nn : 0 ≤ npairs := Nat.cast_nonneg _
  refine ⟨Real.sqrt (C₁ * npairs) * Dmax, by positivity, ?_⟩
  intro T x hx
  set hsn : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ with hhsn_def
  have hhsn_nn : 0 ≤ hsn := norm_nonneg _
  have hx_K : x ∈ Kset := hx
  set yx : EuclN := (toEuclidean (E := E)) ((extChartAt I α) x) with hyx_def
  have hyx_Kc : yx ∈ Kc := by
    rw [hKc_def, hyx_def]
    exact ⟨(extChartAt I α) x, ⟨x, hx_K, rfl⟩, rfl⟩
  have hpull_x : (extChartAt I α).symm ((toEuclidean (E := E)).symm yx) = x := by
    rw [hyx_def]; exact hpull_eq x hx_K
  have h_core := hC₁ T x hx_K
  have h_each : ∀ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)),
      (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x) ^ 2 ≤
        (Dmax * hsn) ^ 2 := by
    intro IJ
    have h := hDfun IJ T yx hyx_Kc
    rw [hpull_x] at h
    have hDle : Dfun IJ ≤ Dmax := by
      rw [hDmax_def]
      exact le_sup_of_le_left (Finset.le_sup' Dfun (Finset.mem_univ IJ))
    have h' : |tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x|
        ≤ Dmax * hsn :=
      h.trans (mul_le_mul_of_nonneg_right hDle hhsn_nn)
    have habs_nn : 0 ≤ |tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x| :=
      abs_nonneg _
    have hDhsn_nn : 0 ≤ Dmax * hsn := mul_nonneg hDmax_nn hhsn_nn
    calc (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x) ^ 2
        = |tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x| ^ 2 := (sq_abs _).symm
      _ ≤ (Dmax * hsn) ^ 2 := by
          exact pow_le_pow_left₀ habs_nn h' 2
  have h_sum_sq : (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x) ^ 2)
        ≤ npairs * (Dmax * hsn) ^ 2 := by
    rw [hnp_def]
    rw [← Fintype.sum_prod_type']
    refine (Finset.sum_le_sum (fun IJ _ => h_each IJ)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_sq : ‖T.toSection x‖ ^ 2 ≤ (Real.sqrt (C₁ * npairs) * Dmax) ^ 2 * hsn ^ 2 := by
    refine h_core.trans ?_
    calc C₁ * (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x) ^ 2)
        ≤ C₁ * (npairs * (Dmax * hsn) ^ 2) :=
          mul_le_mul_of_nonneg_left h_sum_sq (le_of_lt hC₁_pos)
      _ = (Real.sqrt (C₁ * npairs) * Dmax) ^ 2 * hsn ^ 2 := by
          have hsq : Real.sqrt (C₁ * npairs) ^ 2 = C₁ * npairs :=
            Real.sq_sqrt (by positivity)
          nlinarith [hsq]
  have hsec_nn : 0 ≤ ‖T.toSection x‖ := norm_nonneg _
  have hconst_nn : 0 ≤ Real.sqrt (C₁ * npairs) * Dmax := by positivity
  have h_rhs_sq : (Real.sqrt (C₁ * npairs) * Dmax) ^ 2 * hsn ^ 2 =
      (Real.sqrt (C₁ * npairs) * Dmax * hsn) ^ 2 := by ring
  rw [h_rhs_sq] at h_sq
  calc ‖T.toSection x‖ = Real.sqrt (‖T.toSection x‖ ^ 2) := (Real.sqrt_sq hsec_nn).symm
    _ ≤ Real.sqrt ((Real.sqrt (C₁ * npairs) * Dmax * hsn) ^ 2) := Real.sqrt_le_sqrt h_sq
    _ = Real.sqrt (C₁ * npairs) * Dmax * hsn :=
        Real.sqrt_sq (by positivity)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [BoundarylessManifold I M] in
theorem tensorPouSobolevHilbert_embedding_Ck_gNorm
    (g : SmoothRiemannianMetric I M) (r s k m : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 2 * m) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g r s) (x : M),
        ‖T.toSection x‖ ≤
          C * ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  classical
  have hk : (Module.finrank ℝ E : ℝ) < 2 * (2 * k) := by
    have : Module.finrank ℝ E < 2 * (2 * k) := by omega
    exact_mod_cast this
  rcases isEmpty_or_nonempty M with hMempty | hMne
  · exact ⟨1, one_pos, fun _T x => (hMempty.false x).elim⟩
  obtain ⟨x₀⟩ := hMne
  set S : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have hS_ne : S.Nonempty := by
    have hsum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x₀
    rw [← hS_def] at hsum
    rcases Finset.eq_empty_or_nonempty S with hSe | hSne
    · exfalso; rw [hSe] at hsum; simp at hsum
    · exact hSne
  set N : ℕ := S.card with hN_def
  have hN_pos : 0 < N := Finset.card_pos.mpr hS_ne
  have hN_pos_real : (0 : ℝ) < N := by exact_mod_cast hN_pos
  have hcN_pos : (0 : ℝ) < 1 / N := by positivity
  have h_perchart : ∀ α : M, ∃ Dα : ℝ, 0 ≤ Dα ∧ ∀ (T : SmoothCcTensor g r s),
      ∀ x ∈ {x : M | (1 / N : ℝ) ≤ (chartAtlasPOU I M α : M → ℝ) x},
        ‖T.toSection x‖ ≤ Dα *
          ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ := fun α =>
    chartFiberNorm_le_hsNorm_on_superlevel (I := I) (M := M) g r s k hk α hcN_pos
  choose Dfun hDfun_nn hDfun using h_perchart
  set C : ℝ := S.sup' hS_ne Dfun + 1 with hC_def
  have hSsup_nn : 0 ≤ S.sup' hS_ne Dfun := by
    obtain ⟨β, hβ⟩ := hS_ne
    exact le_trans (hDfun_nn β) (Finset.le_sup' Dfun hβ)
  have hC_pos : 0 < C := by rw [hC_def]; linarith
  refine ⟨C, hC_pos, fun T x => ?_⟩
  have hsum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  rw [← hS_def] at hsum
  have h_exists_α : ∃ α ∈ S, (1 / N : ℝ) ≤ (chartAtlasPOU I M α : M → ℝ) x := by
    by_contra h_all
    push Not at h_all
    have h_sum_lt : (∑ α ∈ S, (chartAtlasPOU I M α : M → ℝ) x) < ∑ _α ∈ S, (1 / N : ℝ) :=
      Finset.sum_lt_sum_of_nonempty hS_ne (fun α hα => h_all α hα)
    rw [Finset.sum_const, hsum, nsmul_eq_mul, ← hN_def, mul_one_div,
      div_self hN_pos_real.ne'] at h_sum_lt
    exact lt_irrefl 1 h_sum_lt
  obtain ⟨α, hα_S, hα_ge⟩ := h_exists_α
  have h_bound := hDfun α T x hα_ge
  refine h_bound.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [hC_def]
  have hDα_le : Dfun α ≤ S.sup' hS_ne Dfun := Finset.le_sup' Dfun hα_S
  linarith

end DifferentialGeometry.PDE.RicciFlow

end
