import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseOrderPeeling
import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedHsNormReverseOrderZero
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqLeRawComponents
import Mathlib.Algebra.Order.Chebyshev

noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Topology Metric Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
private lemma mem_chartImagePOUTsupport_of_pou_pos
    (α : M) {y : EuclN}
    (hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α)
    (hpos : 0 < (chartAtlasPOU I M α : M → ℝ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) :
    y ∈ chartImagePOUTsupport (I := I) (M := M) α := by
  obtain ⟨z, hz_tgt, hz_eq⟩ := hy_target
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  have hx_supp : x ∈ tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    subset_tsupport _ (ne_of_gt hpos)
  have hsymm : (toEuclidean (E := E)).symm y = z := by
    rw [← hz_eq]
    exact (toEuclidean (E := E)).symm_apply_apply z
  have hext : (extChartAt I α) x = z := by
    rw [hx_def, hsymm]
    exact (extChartAt I α).right_inv hz_tgt
  refine ⟨(extChartAt I α) x, ⟨x, hx_supp, rfl⟩, ?_⟩
  rw [hext, hz_eq]

omit [BoundarylessManifold I M] in
private theorem eLpNorm_abs_rawPullR_ball_le_tensorL2Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {y₀ : EuclN} {R c : ℝ} (hc_pos : 0 < c)
    (hball_sub : Metric.ball y₀ R ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hρ_lb : ∀ y ∈ Metric.ball y₀ R,
      c ≤ (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (S : SmoothCcTensor g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      eLpNorm (fun z => |tensorComponentEuclideanChart (I := I) (M := M) g r s S α Idx Jdx z|) 2
          ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) ≤
        ENNReal.ofReal ((Real.sqrt c⁻¹ * B) *
          tensorL2Norm (I := I) (M := M) g r s S.toFun) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    tensorPouSobolevHsNorm_zero_le_tensorL2Norm (I := I) (M := M) g r s
  refine ⟨CA, hCA_nn, ?_⟩
  intro S Idx Jdx
  have habs_eq : (fun z : EuclN =>
      |tensorComponentEuclideanChart (I := I) (M := M) g r s S α Idx Jdx z|) =ᵐ[
      (volume : Measure EuclN).restrict (Metric.ball y₀ R)]
      (fun z : EuclN => ‖iteratedFDeriv ℝ 0
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) z‖) := by
    refine Filter.Eventually.of_forall (fun z => ?_)
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    rfl
  rw [eLpNorm_congr_ae habs_eq]
  set X : ℝ≥0∞ := eLpNorm (fun z : EuclN => ‖iteratedFDeriv ℝ 0
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) z‖) 2
    ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) with hX_def
  have h_key := eLpNorm_sq_iteratedFDeriv_le_hsBlock (I := I) (M := M)
    g r s S α ⟨Idx, Jdx⟩ 0 hc_pos hball_sub hρ_lb
  have h_blk := hsBlock_le_hsNorm_sq (I := I) (M := M) g 0 S α ⟨Idx, Jdx⟩ 0
    (Finset.mem_range.mpr (by omega))
  have hX_sq : X ^ 2 ≤
      ENNReal.ofReal (((Module.finrank ℝ E ^ 0 : ℕ) : ℝ) * c⁻¹) *
        (tensorPouSobolevHsNorm (I := I) (M := M) g 0 S) ^ 2 := by
    rw [hX_def]
    exact h_key.trans (mul_le_mul_of_nonneg_left h_blk (zero_le _))
  set L : ℝ := tensorL2Norm (I := I) (M := M) g r s S.toFun with hL_def
  have hL_nn : 0 ≤ L := tensorL2Norm_nonneg (I := I) (M := M) g r s S.toFun
  have h_hs_ne : tensorPouSobolevHsNorm (I := I) (M := M) g 0 S ≠ ⊤ :=
    (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g 0 S).ne
  have h_rhs_ne :
      ENNReal.ofReal (((Module.finrank ℝ E ^ 0 : ℕ) : ℝ) * c⁻¹) *
        (tensorPouSobolevHsNorm (I := I) (M := M) g 0 S) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top h_hs_ne)
  have hX_ne : X ≠ ⊤ := by
    intro hX_top
    have : X ^ 2 = ⊤ := by rw [hX_top]; simp
    rw [this] at hX_sq
    exact h_rhs_ne (top_le_iff.mp hX_sq)
  have h_toReal := ENNReal.toReal_mono h_rhs_ne hX_sq
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow] at h_toReal
  have h_hs_le : (tensorPouSobolevHsNorm (I := I) (M := M) g 0 S).toReal ≤
      CA * L := hCA S
  have hone : ((Module.finrank ℝ E ^ 0 : ℕ) : ℝ) = 1 := by norm_num
  have h_hs_toReal_nn :
      0 ≤ (tensorPouSobolevHsNorm (I := I) (M := M) g 0 S).toReal :=
    ENNReal.toReal_nonneg
  have hXr_sq : X.toReal ^ 2 ≤ c⁻¹ * (CA * L) ^ 2 := by
    have h_sq_le : (tensorPouSobolevHsNorm (I := I) (M := M) g 0 S).toReal ^ 2 ≤
        (CA * L) ^ 2 := pow_le_pow_left₀ h_hs_toReal_nn h_hs_le 2
    calc X.toReal ^ 2
        ≤ ((Module.finrank ℝ E ^ 0 : ℕ) : ℝ) * c⁻¹ *
            (tensorPouSobolevHsNorm (I := I) (M := M) g 0 S).toReal ^ 2 := h_toReal
      _ = c⁻¹ * (tensorPouSobolevHsNorm (I := I) (M := M) g 0 S).toReal ^ 2 := by
          rw [hone, one_mul]
      _ ≤ c⁻¹ * (CA * L) ^ 2 := by
          refine mul_le_mul_of_nonneg_left h_sq_le ?_
          positivity
  have hc_inv_nn : (0 : ℝ) ≤ c⁻¹ := by positivity
  have hXr_le : X.toReal ≤ Real.sqrt c⁻¹ * (CA * L) := by
    have h_sq : X.toReal ^ 2 ≤ (Real.sqrt c⁻¹ * (CA * L)) ^ 2 := by
      have hs : Real.sqrt c⁻¹ ^ 2 = c⁻¹ := Real.sq_sqrt hc_inv_nn
      nlinarith [hXr_sq, hs]
    have hXr_nn : 0 ≤ X.toReal := ENNReal.toReal_nonneg
    calc X.toReal = Real.sqrt (X.toReal ^ 2) := (Real.sqrt_sq hXr_nn).symm
      _ ≤ Real.sqrt ((Real.sqrt c⁻¹ * (CA * L)) ^ 2) := Real.sqrt_le_sqrt h_sq
      _ = Real.sqrt c⁻¹ * (CA * L) := Real.sqrt_sq (by positivity)
  calc X = ENNReal.ofReal X.toReal := (ENNReal.ofReal_toReal hX_ne).symm
    _ ≤ ENNReal.ofReal ((Real.sqrt c⁻¹ * CA) * L) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc X.toReal ≤ Real.sqrt c⁻¹ * (CA * L) := hXr_le
          _ = (Real.sqrt c⁻¹ * CA) * L := by ring

omit [BoundarylessManifold I M] in
private theorem sharpRawPullCenter_le_jetSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)))
    {y₀ : EuclN} {R c : ℝ} (hR : 0 < R) (hc_pos : 0 < c)
    (hball : Metric.closedBall y₀ R ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hρ_lb : ∀ y ∈ Metric.ball y₀ R,
      c ≤ (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) :
    ∃ Cα : ℝ, 0 ≤ Cα ∧ ∀ (T : SmoothCcTensor g r s),
      ∀ y₁ ∈ Metric.ball y₀ (R / 4),
      |tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y₁))|
        ≤ Cα * ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            tensorL2Norm (I := I) (M := M) g r (s + i)
              (iteratedCovGrad g r s i T).toFun := by
  classical
  have hball_open : Metric.ball y₀ R ⊆ chartTargetEuclid (I := I) (M := M) α :=
    Metric.ball_subset_closedBall.trans hball
  set m : ℕ := Module.finrank ℝ E / 2 + 1 with hm_def
  have hdm : (Module.finrank ℝ E : ℝ) < 2 * (m : ℝ) := by
    have h : Module.finrank ℝ E < 2 * m := by rw [hm_def]; omega
    exact_mod_cast h
  obtain ⟨Cloc, hCloc_nn, hCloc⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.smooth_localBall_L2_pointwise_embedding_supercritical
      (d := Module.finrank ℝ E) m hdm (x₀ := y₀) (R := R) hR
  have h_mem_pou : ∀ y ∈ Metric.ball y₀ R,
      y ∈ chartImagePOUTsupport (I := I) (M := M) α := by
    intro y hy
    refine mem_chartImagePOUTsupport_of_pou_pos (I := I) (M := M) α
      (hball_open hy) ?_
    exact lt_of_lt_of_le hc_pos (hρ_lb y hy)
  have h_refold : ∀ j : ℕ, ∃ Cj : ℝ, 0 ≤ Cj ∧ (j ≤ m →
      ∀ (T : SmoothCcTensor g r s), ∀ y ∈ Metric.ball y₀ R,
        ‖iteratedFDeriv ℝ j
            (tensorComponentEuclideanChart (I := I) (M := M) g r s T α IJ.1 IJ.2) y‖ ≤
          Cj * ∑ i ∈ Finset.range (j + 1),
            tensorComponentAbsSum (I := I) (M := M) g r (s + i)
              (iteratedCovGrad g r s i T) α y) := by
    intro j
    by_cases hjm : j ≤ m
    · obtain ⟨Cj, hCj_nn, hCj⟩ :=
        iteratedFDeriv_rawPullR_le_zeroContent_sum (I := I) (M := M) g r s α m j hjm
      refine ⟨Cj, hCj_nn, fun _ T y hy => ?_⟩
      have h := hCj T j (le_refl j) 0 (by omega) IJ.1 IJ.2 y (h_mem_pou y hy)
      have hsum : (∑ i ∈ Finset.range (j + 1),
          tensorComponentAbsSum (I := I) (M := M) g r (s + (0 + i))
            (iteratedCovGrad g r s (0 + i) T) α y) =
          ∑ i ∈ Finset.range (j + 1),
            tensorComponentAbsSum (I := I) (M := M) g r (s + i)
              (iteratedCovGrad g r s i T) α y := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Nat.zero_add]
      rw [hsum] at h
      exact h
    · exact ⟨0, le_refl 0, fun h => absurd h hjm⟩
  choose Cjfun hCjfun_nn hCjfun using h_refold
  have h_l2 : ∀ i : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ (S : SmoothCcTensor g r (s + i))
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin (s + i) → Fin (Module.finrank ℝ E)),
      eLpNorm (fun z => |tensorComponentEuclideanChart (I := I) (M := M) g r (s + i) S α Idx Jdx z|) 2
          ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) ≤
        ENNReal.ofReal ((Real.sqrt c⁻¹ * B) *
          tensorL2Norm (I := I) (M := M) g r (s + i) S.toFun) :=
    fun i => eLpNorm_abs_rawPullR_ball_le_tensorL2Norm (I := I) (M := M)
      g r (s + i) α hc_pos hball_open hρ_lb
  choose Bfun hBfun_nn hBfun using h_l2
  have hmem0 : (0 : ℕ) ∈ Finset.range (m + 1) :=
    Finset.mem_range.mpr (Nat.succ_pos m)
  set Cmax : ℝ := (Finset.range (m + 1)).sup' ⟨0, hmem0⟩ Cjfun with hCmax_def
  have hCmax_nn : 0 ≤ Cmax :=
    le_trans (hCjfun_nn 0) (Finset.le_sup' Cjfun hmem0)
  set Kfun : ℕ → ℝ := fun i =>
    (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin (s + i) → Fin (Module.finrank ℝ E))) : ℝ) *
      (Real.sqrt c⁻¹ * Bfun i) with hKfun_def
  have hKfun_nn : ∀ i, 0 ≤ Kfun i := by
    intro i
    rw [hKfun_def]
    have := hBfun_nn i
    positivity
  set Kmax : ℝ := (Finset.range (m + 1)).sup' ⟨0, hmem0⟩ Kfun with hKmax_def
  have hKmax_nn : 0 ≤ Kmax :=
    le_trans (hKfun_nn 0) (Finset.le_sup' Kfun hmem0)
  refine ⟨Cloc * (((m : ℝ) + 1) * (Cmax * Kmax)), by positivity, ?_⟩
  intro T y₁ hy₁
  have hrange : Finset.range (Module.finrank ℝ E / 2 + 2) = Finset.range (m + 1) := by
    congr 1
  rw [hrange]
  set JS : ℝ := ∑ i ∈ Finset.range (m + 1),
    tensorL2Norm (I := I) (M := M) g r (s + i)
      (iteratedCovGrad g r s i T).toFun with hJS_def
  have hJS_nn : 0 ≤ JS := by
    rw [hJS_def]
    exact Finset.sum_nonneg (fun i _ =>
      tensorL2Norm_nonneg (I := I) (M := M) g r (s + i) _)
  obtain ⟨ftil, hftil_smooth, hftil_eq⟩ :=
    exists_global_smooth_eqOn_ball_of_rawPull (I := I) (M := M)
      g r s T α IJ.1 IJ.2 hball
  have h_loc := hCloc (f := ftil) hftil_smooth y₁ hy₁
  have h_eqOn_ball : Set.EqOn ftil
      (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) (Metric.ball y₀ R) :=
    hftil_eq.mono Metric.ball_subset_closedBall
  have h_eLp_eq : ∀ j : ℕ,
      eLpNorm (fun z => ‖iteratedFDeriv ℝ j ftil z‖) 2
          ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) =
        eLpNorm (fun z => ‖iteratedFDeriv ℝ j
            (tensorComponentEuclideanChart (I := I) (M := M) g r s T α IJ.1 IJ.2) z‖) 2
          ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) := by
    intro j
    refine eLpNorm_congr_ae ?_
    refine (ae_restrict_iff' measurableSet_ball).2
      (Filter.Eventually.of_forall (fun z hz => ?_))
    have hball_nhd : Metric.ball y₀ R ∈ nhds z := Metric.isOpen_ball.mem_nhds hz
    have h_ev : ftil =ᶠ[nhds z]
        (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) :=
      Filter.eventuallyEq_of_mem hball_nhd h_eqOn_ball
    have h_iter_eq := (h_ev.iteratedFDeriv ℝ j).eq_of_nhds
    simp only [h_iter_eq]
    rfl
  have h_raw_meas : ∀ (i : ℕ) (q : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin (s + i) → Fin (Module.finrank ℝ E))),
      AEStronglyMeasurable (fun z => |tensorComponentEuclideanChart (I := I) (M := M) g r (s + i)
        (iteratedCovGrad g r s i T) α q.1 q.2 z|)
        ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) := by
    intro i q
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_ball
    exact (((rawPullR_contDiffOn (I := I) (M := M) g r (s + i)
      (iteratedCovGrad g r s i T) α q.1 q.2).continuousOn).mono hball_open).abs
  set Zc : ℕ → EuclN → ℝ := fun i z =>
    tensorComponentAbsSum (I := I) (M := M) g r (s + i) (iteratedCovGrad g r s i T) α z
    with hZc_def
  have hZc_nn : ∀ i z, 0 ≤ Zc i z := fun i z =>
    zeroContentR_nonneg (I := I) (M := M) g r (s + i) _ α z
  have hZc_meas : ∀ i, AEStronglyMeasurable (Zc i)
      ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) := by
    intro i
    have hZc_eq : Zc i = fun z => ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin (s + i) → Fin (Module.finrank ℝ E)),
        |tensorComponentEuclideanChart (I := I) (M := M) g r (s + i)
          (iteratedCovGrad g r s i T) α q.1 q.2 z| := rfl
    rw [hZc_eq]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_ball
    refine continuousOn_finset_sum _ (fun q _ => ?_)
    exact (((rawPullR_contDiffOn (I := I) (M := M) g r (s + i)
      (iteratedCovGrad g r s i T) α q.1 q.2).continuousOn).mono hball_open).abs
  have h_zc_le : ∀ i ∈ Finset.range (m + 1),
      eLpNorm (Zc i) 2 ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) ≤
        ENNReal.ofReal (Kfun i *
          tensorL2Norm (I := I) (M := M) g r (s + i)
            (iteratedCovGrad g r s i T).toFun) := by
    intro i _
    have hZc_sum : Zc i = ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin (s + i) → Fin (Module.finrank ℝ E)),
        (fun z => |tensorComponentEuclideanChart (I := I) (M := M) g r (s + i)
          (iteratedCovGrad g r s i T) α q.1 q.2 z|) := by
      funext z
      rw [Finset.sum_apply]
      rfl
    calc eLpNorm (Zc i) 2 ((volume : Measure EuclN).restrict (Metric.ball y₀ R))
        ≤ ∑ q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin (s + i) → Fin (Module.finrank ℝ E)),
            eLpNorm (fun z => |tensorComponentEuclideanChart (I := I) (M := M) g r (s + i)
              (iteratedCovGrad g r s i T) α q.1 q.2 z|) 2
              ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) := by
          rw [hZc_sum]
          exact eLpNorm_sum_le (fun q _ => h_raw_meas i q) (by norm_num)
      _ ≤ ∑ _q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin (s + i) → Fin (Module.finrank ℝ E)),
            ENNReal.ofReal ((Real.sqrt c⁻¹ * Bfun i) *
              tensorL2Norm (I := I) (M := M) g r (s + i)
                (iteratedCovGrad g r s i T).toFun) :=
          Finset.sum_le_sum (fun q _ => hBfun i (iteratedCovGrad g r s i T) q.1 q.2)
      _ = ENNReal.ofReal (Kfun i *
            tensorL2Norm (I := I) (M := M) g r (s + i)
              (iteratedCovGrad g r s i T).toFun) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hKfun_def,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          ring
  have h_perj : ∀ j ∈ Finset.range (m + 1),
      (eLpNorm (fun z => ‖iteratedFDeriv ℝ j
          (tensorComponentEuclideanChart (I := I) (M := M) g r s T α IJ.1 IJ.2) z‖) 2
        ((volume : Measure EuclN).restrict (Metric.ball y₀ R))).toReal ≤
        Cmax * (Kmax * JS) := by
    intro j hj
    have hjm : j ≤ m := by
      rw [Finset.mem_range] at hj
      omega
    have h_pt : ∀ y ∈ Metric.ball y₀ R,
        ‖iteratedFDeriv ℝ j (tensorComponentEuclideanChart (I := I) (M := M) g r s T α IJ.1 IJ.2) y‖ ≤
          Cjfun j * ∑ i ∈ Finset.range (m + 1), Zc i y := by
      intro y hy
      refine (hCjfun j hjm T y hy).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCjfun_nn j)
      have hsubset : Finset.range (j + 1) ⊆ Finset.range (m + 1) :=
        Finset.range_subset_range.mpr (Nat.add_le_add_right hjm 1)
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun i _ _ => hZc_nn i y)
    have h_mono : eLpNorm (fun z => ‖iteratedFDeriv ℝ j
        (tensorComponentEuclideanChart (I := I) (M := M) g r s T α IJ.1 IJ.2) z‖) 2
        ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) ≤
        eLpNorm (Cjfun j • fun z => ∑ i ∈ Finset.range (m + 1), Zc i z) 2
          ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) := by
      refine eLpNorm_mono_ae ?_
      refine (ae_restrict_iff' measurableSet_ball).2
        (Filter.Eventually.of_forall (fun z hz => ?_))
      have h2 : 0 ≤ Cjfun j * ∑ i ∈ Finset.range (m + 1), Zc i z :=
        mul_nonneg (hCjfun_nn j) (Finset.sum_nonneg (fun i _ => hZc_nn i z))
      calc ‖‖iteratedFDeriv ℝ j
              (tensorComponentEuclideanChart (I := I) (M := M) g r s T α IJ.1 IJ.2) z‖‖
          = ‖iteratedFDeriv ℝ j
              (tensorComponentEuclideanChart (I := I) (M := M) g r s T α IJ.1 IJ.2) z‖ := norm_norm _
        _ ≤ Cjfun j * ∑ i ∈ Finset.range (m + 1), Zc i z := h_pt z hz
        _ = ‖(Cjfun j • fun z' => ∑ i ∈ Finset.range (m + 1), Zc i z') z‖ := by
            rw [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg h2]
    have h_sum_fun : (fun z => ∑ i ∈ Finset.range (m + 1), Zc i z) =
        ∑ i ∈ Finset.range (m + 1), Zc i := by
      funext z
      rw [Finset.sum_apply]
    have h_enn : eLpNorm (fun z => ‖iteratedFDeriv ℝ j
        (tensorComponentEuclideanChart (I := I) (M := M) g r s T α IJ.1 IJ.2) z‖) 2
        ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) ≤
        ENNReal.ofReal (Cjfun j) *
          ∑ i ∈ Finset.range (m + 1),
            eLpNorm (Zc i) 2 ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) := by
      refine h_mono.trans ?_
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (hCjfun_nn j)]
      refine mul_le_mul_right ?_ _
      rw [h_sum_fun]
      exact eLpNorm_sum_le (fun i _ => hZc_meas i) (by norm_num)
    have h_enn2 : eLpNorm (fun z => ‖iteratedFDeriv ℝ j
        (tensorComponentEuclideanChart (I := I) (M := M) g r s T α IJ.1 IJ.2) z‖) 2
        ((volume : Measure EuclN).restrict (Metric.ball y₀ R)) ≤
        ENNReal.ofReal (Cjfun j * ∑ i ∈ Finset.range (m + 1),
          Kfun i * tensorL2Norm (I := I) (M := M) g r (s + i)
            (iteratedCovGrad g r s i T).toFun) := by
      refine h_enn.trans ?_
      calc ENNReal.ofReal (Cjfun j) *
            ∑ i ∈ Finset.range (m + 1),
              eLpNorm (Zc i) 2 ((volume : Measure EuclN).restrict (Metric.ball y₀ R))
          ≤ ENNReal.ofReal (Cjfun j) *
              ∑ i ∈ Finset.range (m + 1),
                ENNReal.ofReal (Kfun i *
                  tensorL2Norm (I := I) (M := M) g r (s + i)
                    (iteratedCovGrad g r s i T).toFun) :=
            mul_le_mul_right (Finset.sum_le_sum h_zc_le) _
        _ = ENNReal.ofReal (Cjfun j) *
              ENNReal.ofReal (∑ i ∈ Finset.range (m + 1),
                Kfun i * tensorL2Norm (I := I) (M := M) g r (s + i)
                  (iteratedCovGrad g r s i T).toFun) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hKfun_nn i)
              (tensorL2Norm_nonneg (I := I) (M := M) g r (s + i) _))]
        _ = ENNReal.ofReal (Cjfun j * ∑ i ∈ Finset.range (m + 1),
              Kfun i * tensorL2Norm (I := I) (M := M) g r (s + i)
                (iteratedCovGrad g r s i T).toFun) := by
            rw [ENNReal.ofReal_mul (hCjfun_nn j)]
    have h_inner_nn : 0 ≤ Cjfun j * ∑ i ∈ Finset.range (m + 1),
        Kfun i * tensorL2Norm (I := I) (M := M) g r (s + i)
          (iteratedCovGrad g r s i T).toFun := by
      refine mul_nonneg (hCjfun_nn j) (Finset.sum_nonneg (fun i _ => ?_))
      exact mul_nonneg (hKfun_nn i)
        (tensorL2Norm_nonneg (I := I) (M := M) g r (s + i) _)
    have h_tr := ENNReal.toReal_le_of_le_ofReal h_inner_nn h_enn2
    refine h_tr.trans ?_
    have h_inner_le : (∑ i ∈ Finset.range (m + 1),
        Kfun i * tensorL2Norm (I := I) (M := M) g r (s + i)
          (iteratedCovGrad g r s i T).toFun) ≤ Kmax * JS := by
      rw [hJS_def, Finset.mul_sum]
      refine Finset.sum_le_sum (fun i hi => ?_)
      exact mul_le_mul_of_nonneg_right (Finset.le_sup' Kfun hi)
        (tensorL2Norm_nonneg (I := I) (M := M) g r (s + i) _)
    calc Cjfun j * ∑ i ∈ Finset.range (m + 1),
          Kfun i * tensorL2Norm (I := I) (M := M) g r (s + i)
            (iteratedCovGrad g r s i T).toFun
        ≤ Cjfun j * (Kmax * JS) :=
          mul_le_mul_of_nonneg_left h_inner_le (hCjfun_nn j)
      _ ≤ Cmax * (Kmax * JS) :=
          mul_le_mul_of_nonneg_right (Finset.le_sup' Cjfun hj)
            (mul_nonneg hKmax_nn hJS_nn)
  have hy₁_cb : y₁ ∈ Metric.closedBall y₀ R :=
    ((Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall) hy₁
  have hftil_y1 : ftil y₁ =
      tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y₁)) := by
    have := hftil_eq hy₁_cb
    simpa [Function.comp_apply] using this
  calc |tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y₁))|
      = ‖ftil y₁‖ := by rw [hftil_y1, Real.norm_eq_abs]
    _ ≤ Cloc * ∑ j ∈ Finset.range (m + 1),
          (eLpNorm (fun z => ‖iteratedFDeriv ℝ j ftil z‖) 2
            ((volume : Measure EuclN).restrict (Metric.ball y₀ R))).toReal := h_loc
    _ = Cloc * ∑ j ∈ Finset.range (m + 1),
          (eLpNorm (fun z => ‖iteratedFDeriv ℝ j
              (tensorComponentEuclideanChart (I := I) (M := M) g r s T α IJ.1 IJ.2) z‖) 2
            ((volume : Measure EuclN).restrict (Metric.ball y₀ R))).toReal := by
        congr 1
        exact Finset.sum_congr rfl (fun j _ => by rw [h_eLp_eq j])
    _ ≤ Cloc * ∑ _j ∈ Finset.range (m + 1), Cmax * (Kmax * JS) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum h_perj) hCloc_nn
    _ = Cloc * (((m : ℝ) + 1) * (Cmax * (Kmax * JS))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = Cloc * (((m : ℝ) + 1) * (Cmax * Kmax)) * JS := by ring

omit [BoundarylessManifold I M] in
private theorem sharpUniformRawPull_le_jetSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (IJ : (Fin r → Fin (Module.finrank ℝ E)) × (Fin s → Fin (Module.finrank ℝ E)))
    {Kc O : Set EuclN} {c : ℝ} (hc_pos : 0 < c)
    (hKc_compact : IsCompact Kc) (hO_open : IsOpen O)
    (hKcO : Kc ⊆ O) (hO_sub : O ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hρ_lb : ∀ y ∈ O,
      c ≤ (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : SmoothCcTensor g r s), ∀ y ∈ Kc,
      |tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))|
        ≤ D * ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            tensorL2Norm (I := I) (M := M) g r (s + i)
              (iteratedCovGrad g r s i T).toFun := by
  classical
  rcases Set.eq_empty_or_nonempty Kc with hKc_empty | hKc_ne
  · exact ⟨0, le_refl 0, fun T y hy => by
      rw [hKc_empty] at hy
      exact absurd hy (Set.notMem_empty y)⟩
  obtain ⟨δ, hδ_pos, hδ_ball⟩ :=
    lebesgue_number_lemma_of_metric (s := Kc) (c := fun _ : Unit => O)
      hKc_compact (fun _ => hO_open)
      (by intro x hx; exact Set.mem_iUnion.mpr ⟨(), hKcO hx⟩)
  have hδ_sub : ∀ y ∈ Kc, Metric.ball y δ ⊆ O := by
    intro y hy
    obtain ⟨_, hsub⟩ := hδ_ball y hy
    exact hsub
  have hδ2_pos : 0 < δ / 2 := by linarith
  have h_center : ∀ y : Kc, ∃ Cy : ℝ, 0 ≤ Cy ∧ ∀ (T : SmoothCcTensor g r s),
      ∀ y₁ ∈ Metric.ball (y : EuclN) ((δ / 2) / 4),
      |tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y₁))|
        ≤ Cy * ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            tensorL2Norm (I := I) (M := M) g r (s + i)
              (iteratedCovGrad g r s i T).toFun := by
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
    exact sharpRawPullCenter_le_jetSum (I := I) (M := M) g r s α IJ
      hδ2_pos hc_pos hcb_sub hρ_ball
  choose Cfun hCfun_nn hCfun using h_center
  obtain ⟨tcov, htcov⟩ :=
    hKc_compact.elim_finite_subcover
      (U := fun y : Kc => Metric.ball (y : EuclN) ((δ / 2) / 4))
      (fun y => Metric.isOpen_ball)
      (by
        intro z hz
        refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
        rw [Metric.mem_ball, dist_self]
        positivity)
  set Dmax : ℝ := (tcov.image Cfun).sup' (by
    rcases hKc_ne with ⟨z, hz⟩
    obtain ⟨y, hy_t, _⟩ := Set.mem_iUnion₂.mp (htcov hz)
    exact Finset.image_nonempty.mpr ⟨y, hy_t⟩) id ⊔ 0 with hDmax_def
  have hDmax_nn : 0 ≤ Dmax := le_sup_right
  refine ⟨Dmax, hDmax_nn, ?_⟩
  intro T y hy
  set jsn : ℝ := ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
    tensorL2Norm (I := I) (M := M) g r (s + i)
      (iteratedCovGrad g r s i T).toFun with hjsn_def
  have hjsn_nn : 0 ≤ jsn := by
    rw [hjsn_def]
    exact Finset.sum_nonneg (fun i _ =>
      tensorL2Norm_nonneg (I := I) (M := M) g r (s + i) _)
  obtain ⟨yi, hyi_t, hy_in⟩ := Set.mem_iUnion₂.mp (htcov hy)
  have h_bound := hCfun yi T y hy_in
  have hCyi_le : Cfun yi ≤ Dmax := by
    rw [hDmax_def]
    refine le_sup_of_le_left ?_
    exact Finset.le_sup' id (Finset.mem_image_of_mem Cfun hyi_t)
  calc |tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))|
      ≤ Cfun yi * jsn := h_bound
    _ ≤ Dmax * jsn := mul_le_mul_of_nonneg_right hCyi_le hjsn_nn

omit [BoundarylessManifold I M] in
private theorem sharpFiberNormSq_le_jetSum_on_superlevel
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {c : ℝ} (hc_pos : 0 < c) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : SmoothCcTensor g r s),
      ∀ x ∈ {x : M | c ≤ (chartAtlasPOU I M α : M → ℝ) x},
        riemannianFiberNormSq (I := I) (M := M) g r s x (T.toSection x) ≤
          D * (∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            tensorL2Norm (I := I) (M := M) g r (s + i)
              (iteratedCovGrad g r s i T).toFun) ^ 2 := by
  classical
  set Kset : Set M := {x : M | c ≤ (chartAtlasPOU I M α : M → ℝ) x} with hKset_def
  have hρ_cont : Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous
  have hclosed : IsClosed Kset := isClosed_le continuous_const hρ_cont
  have hK_compact : IsCompact Kset := hclosed.isCompact
  have hK_sub : Kset ⊆ (chartAt H α).source := by
    intro x hx
    have hx_pos : (0 : ℝ) < (chartAtlasPOU I M α : M → ℝ) x :=
      lt_of_lt_of_le hc_pos hx
    have hx_supp : x ∈ Function.support
        (fun y : M => (chartAtlasPOU I M α : M → ℝ) y) := ne_of_gt hx_pos
    have hx_tsupp : x ∈ tsupport
        (fun y : M => (chartAtlasPOU I M α : M → ℝ) y) :=
      subset_tsupport _ hx_supp
    exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate
      I M α hx_tsupp
  obtain ⟨C₁, hC₁_nn, hC₁⟩ :=
    riemannianFiberNormSq_le_raw_components_on_pouTsupport (I := I) (M := M) g r s α
  set Kc : Set EuclN :=
    (toEuclidean (E := E)) '' ((extChartAt I α) '' Kset) with hKc_def
  have hKc_compact : IsCompact Kc := by
    have h1 : IsCompact ((extChartAt I α) '' Kset) :=
      hK_compact.image_of_continuousOn
        ((continuousOn_extChartAt α).mono (by
          intro x hx
          rw [extChartAt_source]
          exact hK_sub hx))
    exact h1.image (toEuclidean (E := E)).continuous
  set O : Set EuclN :=
    chartTargetEuclid (I := I) (M := M) α ∩
      (fun y : EuclN => (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ⁻¹' (Set.Ioi (c / 2))
    with hO_def
  have hO_open : IsOpen O := by
    rw [hO_def]
    have hcontOn : ContinuousOn
        (fun y : EuclN => (chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (chartTargetEuclid (I := I) (M := M) α) :=
      hρ_cont.comp_continuousOn'
        (DifferentialGeometry.Analysis.Sobolev.Chart.continuousOn_symm_toEuclideanSymm
          (I := I) (M := M) α)
    exact hcontOn.isOpen_inter_preimage
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
        (I := I) (M := M) α)
      isOpen_Ioi
  have hO_sub : O ⊆ chartTargetEuclid (I := I) (M := M) α := by
    rw [hO_def]
    exact Set.inter_subset_left
  have hx_ext_src : ∀ x ∈ Kset, x ∈ (extChartAt I α).source := by
    intro x hx
    rw [extChartAt_source]
    exact hK_sub hx
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
    have hy_eq : y = (toEuclidean (E := E)) ((extChartAt I α) x) := by
      rw [hxz]
      exact hzy.symm
    have hpull : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = x := by
      rw [hy_eq]
      exact hpull_eq x hx_K
    have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) α := by
      rw [hy_eq]
      exact ⟨(extChartAt I α) x, (extChartAt I α).map_source (hx_ext_src x hx_K), rfl⟩
    refine ⟨hy_target, ?_⟩
    have hgoal : c / 2 < (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
      rw [hpull]
      have hx_ge : c ≤ (chartAtlasPOU I M α : M → ℝ) x := hx_K
      linarith
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
      ∃ Dij : ℝ, 0 ≤ Dij ∧ ∀ (T : SmoothCcTensor g r s), ∀ y ∈ Kc,
        |tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))|
          ≤ Dij * ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
              tensorL2Norm (I := I) (M := M) g r (s + i)
                (iteratedCovGrad g r s i T).toFun := by
    intro IJ
    exact sharpUniformRawPull_le_jetSum (I := I) (M := M) g r s α IJ hc2_pos
      hKc_compact hO_open hKcO hO_sub hρ_on_O
  choose Dfun hDfun_nn hDfun using h_comp
  set Dmax : ℝ := (Finset.univ.sup' (Finset.univ_nonempty) Dfun) ⊔ 0 with hDmax_def
  have hDmax_nn : 0 ≤ Dmax := le_sup_right
  set npairs : ℝ := (Fintype.card ((Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) : ℝ) with hnp_def
  have hnp_nn : 0 ≤ npairs := Nat.cast_nonneg _
  refine ⟨C₁ * npairs * Dmax ^ 2, by positivity, ?_⟩
  intro T x hx
  set jsn : ℝ := ∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
    tensorL2Norm (I := I) (M := M) g r (s + i)
      (iteratedCovGrad g r s i T).toFun with hjsn_def
  have hjsn_nn : 0 ≤ jsn := by
    rw [hjsn_def]
    exact Finset.sum_nonneg (fun i _ =>
      tensorL2Norm_nonneg (I := I) (M := M) g r (s + i) _)
  have hx_K : x ∈ Kset := hx
  have hx_pos : (0 : ℝ) < (chartAtlasPOU I M α : M → ℝ) x :=
    lt_of_lt_of_le hc_pos hx_K
  have hx_tsupp : x ∈ tsupport
      (fun y : M => (chartAtlasPOU I M α : M → ℝ) y) :=
    subset_tsupport _ (ne_of_gt hx_pos)
  have h_core := hC₁ T hx_tsupp
  set yx : EuclN := (toEuclidean (E := E)) ((extChartAt I α) x) with hyx_def
  have hyx_Kc : yx ∈ Kc := by
    rw [hKc_def, hyx_def]
    exact ⟨(extChartAt I α) x, ⟨x, hx_K, rfl⟩, rfl⟩
  have hpull_x : (extChartAt I α).symm ((toEuclidean (E := E)).symm yx) = x := by
    rw [hyx_def]
    exact hpull_eq x hx_K
  have h_each : ∀ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)),
      (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x) ^ 2 ≤
        (Dmax * jsn) ^ 2 := by
    intro IJ
    have h := hDfun IJ T yx hyx_Kc
    rw [hpull_x] at h
    have hDle : Dfun IJ ≤ Dmax := by
      rw [hDmax_def]
      exact le_sup_of_le_left (Finset.le_sup' Dfun (Finset.mem_univ IJ))
    have h' : |tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x|
        ≤ Dmax * jsn := by
      refine h.trans ?_
      rw [← hjsn_def]
      exact mul_le_mul_of_nonneg_right hDle hjsn_nn
    calc (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x) ^ 2
        = |tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2 x| ^ 2 :=
          (sq_abs _).symm
      _ ≤ (Dmax * jsn) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h' 2
  have h_sum_sq : (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x) ^ 2)
        ≤ npairs * (Dmax * jsn) ^ 2 := by
    rw [hnp_def, ← Fintype.sum_prod_type']
    refine (Finset.sum_le_sum (fun IJ _ => h_each IJ)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc riemannianFiberNormSq (I := I) (M := M) g r s x (T.toSection x)
      ≤ C₁ * (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x) ^ 2) :=
        h_core
    _ ≤ C₁ * (npairs * (Dmax * jsn) ^ 2) :=
        mul_le_mul_of_nonneg_left h_sum_sq hC₁_nn
    _ = C₁ * npairs * Dmax ^ 2 * jsn ^ 2 := by ring

omit [BoundarylessManifold I M] in
theorem exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g r s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g r s x (T.toSection x) ≤
          C ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g r s j T‖ ^ 2 := by
  classical
  rcases isEmpty_or_nonempty M with hMempty | hMne
  · exact ⟨0, le_refl 0, fun _T x => (hMempty.false x).elim⟩
  obtain ⟨x₀⟩ := hMne
  set S : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have hS_ne : S.Nonempty := by
    have hsum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x₀
    rw [← hS_def] at hsum
    rcases Finset.eq_empty_or_nonempty S with hSe | hSne
    · exfalso
      rw [hSe] at hsum
      simp at hsum
    · exact hSne
  set N : ℕ := S.card with hN_def
  have hN_pos : 0 < N := Finset.card_pos.mpr hS_ne
  have hN_pos_real : (0 : ℝ) < N := by exact_mod_cast hN_pos
  have hcN_pos : (0 : ℝ) < 1 / N := by positivity
  have h_perchart : ∀ α : M, ∃ Dα : ℝ, 0 ≤ Dα ∧ ∀ (T : SmoothCcTensor g r s),
      ∀ x ∈ {x : M | (1 / N : ℝ) ≤ (chartAtlasPOU I M α : M → ℝ) x},
        riemannianFiberNormSq (I := I) (M := M) g r s x (T.toSection x) ≤
          Dα * (∑ i ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            tensorL2Norm (I := I) (M := M) g r (s + i)
              (iteratedCovGrad g r s i T).toFun) ^ 2 := fun α =>
    sharpFiberNormSq_le_jetSum_on_superlevel (I := I) (M := M) g r s α hcN_pos
  choose Dfun hDfun_nn hDfun using h_perchart
  set Dmax : ℝ := S.sup' hS_ne Dfun ⊔ 0 with hDmax_def
  have hDmax_nn : 0 ≤ Dmax := le_sup_right
  set w : ℕ := Module.finrank ℝ E / 2 + 2 with hw_def
  have hDw_nn : 0 ≤ Dmax * (w : ℝ) := mul_nonneg hDmax_nn (Nat.cast_nonneg w)
  refine ⟨Real.sqrt (Dmax * (w : ℝ)), Real.sqrt_nonneg _, ?_⟩
  intro T x
  have hsum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  rw [← hS_def] at hsum
  have h_exists_α : ∃ α ∈ S, (1 / N : ℝ) ≤ (chartAtlasPOU I M α : M → ℝ) x := by
    by_contra h_all
    push Not at h_all
    have h_sum_lt : (∑ α ∈ S, (chartAtlasPOU I M α : M → ℝ) x) <
        ∑ _α ∈ S, (1 / N : ℝ) :=
      Finset.sum_lt_sum_of_nonempty hS_ne (fun α hα => h_all α hα)
    rw [Finset.sum_const, hsum, nsmul_eq_mul, ← hN_def, mul_one_div,
      div_self hN_pos_real.ne'] at h_sum_lt
    exact lt_irrefl 1 h_sum_lt
  obtain ⟨α, hα_S, hα_ge⟩ := h_exists_α
  have h_bound := hDfun α T x hα_ge
  have hDα_le : Dfun α ≤ Dmax := by
    rw [hDmax_def]
    exact le_sup_of_le_left (Finset.le_sup' Dfun hα_S)
  have hL_eq : ∀ i : ℕ,
      tensorL2Norm (I := I) (M := M) g r (s + i)
        (iteratedCovGrad g r s i T).toFun = ‖iteratedCovGrad (I := I) g r s i T‖ :=
    fun i => DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
      (I := I) (M := M) g (iteratedCovGrad g r s i T)
  have hsum_eq : (∑ i ∈ Finset.range w,
      tensorL2Norm (I := I) (M := M) g r (s + i)
        (iteratedCovGrad g r s i T).toFun) =
      ∑ i ∈ Finset.range w, ‖iteratedCovGrad (I := I) g r s i T‖ :=
    Finset.sum_congr rfl (fun i _ => hL_eq i)
  have hCS : (∑ i ∈ Finset.range w, ‖iteratedCovGrad (I := I) g r s i T‖) ^ 2 ≤
      (w : ℝ) * ∑ i ∈ Finset.range w, ‖iteratedCovGrad (I := I) g r s i T‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range w)
      (f := fun i => ‖iteratedCovGrad (I := I) g r s i T‖)
    simpa using h
  have hjs_nonneg : 0 ≤ ∑ i ∈ Finset.range w,
      ‖iteratedCovGrad (I := I) g r s i T‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  calc riemannianFiberNormSq (I := I) (M := M) g r s x (T.toSection x)
      ≤ Dfun α * (∑ i ∈ Finset.range w,
          tensorL2Norm (I := I) (M := M) g r (s + i)
            (iteratedCovGrad g r s i T).toFun) ^ 2 := h_bound
    _ ≤ Dmax * (∑ i ∈ Finset.range w,
          tensorL2Norm (I := I) (M := M) g r (s + i)
            (iteratedCovGrad g r s i T).toFun) ^ 2 :=
        mul_le_mul_of_nonneg_right hDα_le (sq_nonneg _)
    _ = Dmax * (∑ i ∈ Finset.range w, ‖iteratedCovGrad (I := I) g r s i T‖) ^ 2 := by
        rw [hsum_eq]
    _ ≤ Dmax * ((w : ℝ) * ∑ i ∈ Finset.range w,
          ‖iteratedCovGrad (I := I) g r s i T‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hCS hDmax_nn
    _ = Real.sqrt (Dmax * (w : ℝ)) ^ 2 * ∑ i ∈ Finset.range w,
          ‖iteratedCovGrad (I := I) g r s i T‖ ^ 2 := by
        rw [Real.sq_sqrt hDw_nn]
        ring

end DifferentialGeometry.PDE.RicciFlow

end
