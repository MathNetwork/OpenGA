import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SmoothCoordinateJetPreservation
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.PointwiseSpectralCoordinate
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerModeL2
import DifferentialGeometry.Analysis.Calculus.ContDiffExtendInterval
import DifferentialGeometry.Analysis.Integration.L2.ForcingFiniteOrderTimeRegularityParametricIntegral

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private local instance tensorRSModelNormedAddCommGroup_local :
    NormedAddCommGroup (Tensor0SBundle.TensorRSModel 0 2 ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedAddCommGroup 0 2

private local instance tensorRSModelNormedSpace_local :
    NormedSpace ℝ (Tensor0SBundle.TensorRSModel 0 2 ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace 0 2


section FiniteOrderSpectralPathEngine

open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth
  tensorChartComponentRaw tensorChartComponentProjection tensorChartBasisElement
  toEuclidean_extChartAt_mem_chartTargetEuclid)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem smoothCcTensor_rawChartComponent_eigenSeries_tsum_eq_local
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (d : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (hd : ∀ i, tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) S) i = d i)
    (hmass : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, tensorSobolevWeight (I := I) (M := M) i σ * (d i) ^ 2 ≤ B i)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] Jdx x =
      ∑' i, d i * tensorChartComponentRaw (I := I) (M := M) g 0 2
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x := by
  classical
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) 0 2
  set u : TensorL2 0 2 g := SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) S with hu_def
  have hcoeff_u : ∀ i, tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i = d i := hd
  have hu : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ vH : tensorHs (I := I) (M := M) g 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ vH = u := by
    refine allHs_of_weighted_summable_pub (I := I) (M := M) g u (fun σ hσ => ?_)
    obtain ⟨B, hB_sum, hB_le⟩ := hmass σ hσ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hB_sum
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
    · rw [hcoeff_u i]; exact hB_le i
  set F : ℕ → SmoothCcTensor g 0 2 :=
    fun n => spectralPartialSum (I := I) (M := M) g u n with hF_def
  have hcauchy : ∀ kc : ℕ, CauchySeq (fun n =>
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g) (r := 0) (s := 2) (2 * kc) (F n)) :=
    fun kc => spectralPartialSum_toHs_cauchy (I := I) (M := M) g u hu (2 * kc)
  have hF_L2 : Filter.Tendsto (fun n => (F n : TensorL2 0 2 g)) Filter.atTop (nhds u) :=
    spectralPartialSum_toL2_tendsto (I := I) (M := M) g u
  have hTrep : (S : TensorL2 0 2 g) = u := rfl
  have hsum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  have hexists : ∃ β ∈ chartAtlasPOU_finset (I := I) (M := M),
      0 < ((chartAtlasPOU I M) β : C^∞⟮I, M; ℝ⟯) x := by
    by_contra hcon
    push Not at hcon
    have hzero : ∀ β ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((chartAtlasPOU I M) β : M → ℝ) x = 0 := by
      intro β hβ
      have hle := hcon β hβ
      have hnn := (chartAtlasPOU I M).nonneg β x
      linarith
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at hsum
    exact absurd hsum (by norm_num)
  obtain ⟨β, _hβmem, hβpos⟩ := hexists
  set ρ : ℝ := ((chartAtlasPOU I M) β : C^∞⟮I, M; ℝ⟯) x with hρ_def
  have hx_src : x ∈ (chartAt H β).source := by
    have hsub := chartAtlasPOU_isSubordinate (I := I) (M := M) β
    apply hsub
    exact subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hβpos))
  set yx : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    toEuclidean (extChartAt I β x) with hyx_def
  have hyx_mem := toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) β hx_src
  rw [← hyx_def] at hyx_mem
  have hround : (extChartAt I β).symm (toEuclidean.symm yx) = x := by
    rw [hyx_def, ContinuousLinearEquiv.symm_apply_apply]
    exact (extChartAt I β).left_inv (by rw [extChartAt_source (I := I)]; exact hx_src)
  have hcomp_eq : ∀ (Z : SmoothCcTensor g 0 2) (Q : CompIdx E 0 2),
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent
          (I := I) (M := M) g 0 2 Z β Q.1 Q.2 yx =
        ρ * tensorChartComponentRaw (I := I) (M := M) g 0 2 Z β Q.1 Q.2 x := by
    intro Z Q
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponent_def,
      chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hyx_mem, hround]
    rfl
  have hraw_tendsto : ∀ Q : CompIdx E 0 2,
      Filter.Tendsto
        (fun n => tensorChartComponentRaw (I := I) (M := M) g 0 2 (F n) β Q.1 Q.2 x)
        Filter.atTop
        (nhds (tensorChartComponentRaw (I := I) (M := M) g 0 2 S β Q.1 Q.2 x)) := by
    intro Q
    have hct := spectralChartComponent_tendsto (I := I) (M := M) g u hcauchy hF_L2 S hTrep
      β Q hyx_mem
    simp only [hcomp_eq] at hct
    have hρne : ρ ≠ 0 := ne_of_gt hβpos
    have hscaled := hct.const_mul ρ⁻¹
    simp only [← mul_assoc, inv_mul_cancel₀ hρne, one_mul] at hscaled
    exact hscaled
  have htend_sec : Filter.Tendsto (fun n => ((F n).toSection x :
      Tensor0SBundle.TensorRSSpace 0 2 I x)) Filter.atTop (nhds (S.toSection x)) := by
    have hexpand : ∀ Z : SmoothCcTensor g 0 2, Z.toSection x =
        ∑ Q : CompIdx E 0 2,
          tensorChartComponentRaw (I := I) (M := M) g 0 2 Z β Q.1 Q.2 x •
            chartBasisFiberSection (I := I) (M := M) 0 2 β Q x :=
      fun Z => toSection_eq_sum_chartBasisFiberSection (I := I) (M := M) g 0 2 Z β hx_src
    simp only [hexpand]
    exact tendsto_finset_sum _ (fun Q _ => (hraw_tendsto Q).smul_const _)
  have hLval : ∀ Z : SmoothCcTensor g 0 2,
      tensorChartComponentRaw (I := I) (M := M) g 0 2 Z α ![] Jdx x =
        (tensorChartComponentProjection (E := E) 0 2 ![] Jdx)
          ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
              (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) α).continuousLinearMapAt
            ℝ x (Z.toSection x)) :=
    fun Z => rfl
  have htend_raw : Filter.Tendsto (fun n =>
      tensorChartComponentRaw (I := I) (M := M) g 0 2 (F n) α ![] Jdx x) Filter.atTop
      (nhds (tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] Jdx x)) := by
    simp only [hLval]
    exact ((tensorChartComponentProjection (E := E) 0 2 ![] Jdx).continuous.tendsto _).comp
      ((((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) α).continuousLinearMapAt
          ℝ x).continuous.tendsto _).comp htend_sec)
  have hpartial : ∀ n, tensorChartComponentRaw (I := I) (M := M) g 0 2 (F n) α ![] Jdx x =
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
        d i * tensorChartComponentRaw (I := I) (M := M) g 0 2
          (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x := by
    intro n
    have hFn : F n = finiteEigenCombo (I := I) (M := M) g
        (eigenIdxFinset (I := I) (M := M) g n)
        (fun i => tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i) := rfl
    rw [hFn, tensorChartComponentRaw_finiteEigenCombo (I := I) (M := M) g _ _ α ![] Jdx x]
    exact Finset.sum_congr rfl (fun i _ => by rw [hcoeff_u i])
  obtain ⟨CK, pK, hCK_nn, hCK⟩ :=
    exists_rawComponentRaw_eigen_pointwise_le_lambda_pow (I := I) (M := M) g α Jdx hx
  set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
  have hsW_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < (sW : ℝ) := by
    rw [hsW_def]; push_cast; linarith
  have hbase_pos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  obtain ⟨B2, hB2_sum, hB2⟩ := hmass (2 * ((pK : ℝ) + (sW : ℝ))) (by positivity)
  have hB2_nn : ∀ i, 0 ≤ B2 i := fun i => by
    have h := hB2 i
    have hw := tensorSobolevWeight_pos (I := I) (M := M) i (2 * ((pK : ℝ) + (sW : ℝ)))
    nlinarith [sq_nonneg (d i), hw.le]
  have hsummable : Summable (fun i => d i * tensorChartComponentRaw (I := I) (M := M) g 0 2
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x) := by
    refine Summable.of_norm_bounded
      (g := fun i => CK * (Real.sqrt (B2 i) *
        tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))))
      (Summable.mul_left CK
        (summable_sqrt_mul_weight_neg (I := I) (M := M) g B2 hB2_sum hB2_nn hsW_gt))
      (fun i => ?_)
    have hd_le := abs_le_sqrt_of_weight_sq_le (I := I) (M := M) g i ((pK : ℝ) + (sW : ℝ))
      (hB2 i)
    have hK_le := hCK i
    have hcollapse : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pK : ℝ) + (sW : ℝ)))
        * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (pK : ℕ)
        = tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) := by
      unfold tensorSobolevWeight
      rw [← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) pK,
        ← Real.rpow_add (hbase_pos i)]
      congr 1; ring
    rw [Real.norm_eq_abs, abs_mul]
    calc |d i| * |tensorChartComponentRaw (I := I) (M := M) g 0 2
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x|
        ≤ (Real.sqrt (B2 i) *
            (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pK : ℝ) + (sW : ℝ)))) *
          (CK * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pK) := by
          refine mul_le_mul hd_le hK_le (abs_nonneg _) ?_
          exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (hbase_pos i).le _)
      _ = CK * (Real.sqrt (B2 i) *
            ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pK : ℝ) + (sW : ℝ)))
              * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (pK : ℕ))) := by ring
      _ = CK * (Real.sqrt (B2 i) * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
          rw [hcollapse]
  have htend_tsum : Filter.Tendsto (fun n =>
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
        d i * tensorChartComponentRaw (I := I) (M := M) g 0 2
          (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x) Filter.atTop
      (nhds (∑' i, d i * tensorChartComponentRaw (I := I) (M := M) g 0 2
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x)) :=
    hsummable.hasSum.comp (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g)
  have htend_lhs : Filter.Tendsto (fun n =>
      ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
        d i * tensorChartComponentRaw (I := I) (M := M) g 0 2
          (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x) Filter.atTop
      (nhds (tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] Jdx x)) :=
    htend_raw.congr hpartial
  exact tendsto_nhds_unique htend_lhs htend_tsum

set_option maxHeartbeats 1600000 in
private theorem spectralPathFO_rawCompOnE_euclidean_contDiffOn_local
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (kk : ℕ)
      (fun q : ℝ × E => tensorChartComponentOnModel (I := I) (M := M) g (T_rep q.1) α Jdx q.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  classical
  set Ω : Set E := interior (extChartAt I α).target with hΩ_def
  have hΩ_open : IsOpen Ω := isOpen_interior
  refine contDiffOn_of_locally_contDiffOn ?_
  rintro ⟨t₀, y₀⟩ hmem
  obtain ⟨_ht₀, hy₀⟩ := hmem
  obtain ⟨r, hr_pos, hball_sub⟩ := Metric.isOpen_iff.mp hΩ_open y₀ hy₀
  refine ⟨Set.univ ×ˢ Metric.ball y₀ (r / 2), isOpen_univ.prod Metric.isOpen_ball,
    ⟨Set.mem_univ t₀, Metric.mem_ball_self (by positivity)⟩, ?_⟩
  set B : Set E := Metric.ball y₀ (r / 2) with hB_def
  set Bc : Set E := Metric.closedBall y₀ (r / 2) with hBc_def
  have hball_le : B ⊆ Bc := Metric.ball_subset_closedBall
  have hBc_sub : Bc ⊆ Ω := by
    intro z hz
    rw [hBc_def, Metric.mem_closedBall] at hz
    exact hball_sub (by rw [Metric.mem_ball]; linarith)
  have hB_sub : B ⊆ Ω := hball_le.trans hBc_sub
  have hBc_compact : IsCompact Bc := isCompact_closedBall y₀ (r / 2)
  have hslab_inter :
      (Set.Icc (0 : ℝ) T ×ˢ Ω) ∩ (Set.univ ×ˢ B) = Set.Icc (0 : ℝ) T ×ˢ B := by
    rw [Set.prod_inter_prod, Set.inter_univ, Set.inter_eq_right.mpr hB_sub]
  rw [hslab_inter]
  have hBc_int_ne : (interior Bc).Nonempty := by
    rw [hBc_def, interior_closedBall y₀ (by positivity : (r / 2) ≠ 0)]
    exact ⟨y₀, Metric.mem_ball_self (by positivity)⟩
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) T ×ˢ Bc) :=
    (convex_Icc (0 : ℝ) T).prod (convex_closedBall y₀ (r / 2))
  have huniqBc : UniqueDiffOn ℝ Bc :=
    uniqueDiffOn_convex (convex_closedBall y₀ (r / 2)) hBc_int_ne
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T ×ˢ Bc) :=
    (uniqueDiffOn_Icc hT).prod huniqBc
  have hmajorant := eigenRawIncrementMode_iteratedFDerivWithin_summable_majorant_ofOrder
    (I := I) (M := M) (T := T) g hT kk φ hφ_smooth hmodemass α Jdx
    hBc_compact huniqBc hBc_sub
  set v : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun n => if hn : n ≤ kk then Classical.choose (hmajorant n hn) else 0 with hv_def
  have hv_spec : ∀ (n : ℕ) (hn : n ≤ kk), Summable (v n) ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2) (q : ℝ × E),
        q ∈ Set.Icc (0 : ℝ) T ×ˢ Bc →
        ‖iteratedFDerivWithin ℝ n (eigenRawIncrementMode (I := I) (M := M) g φ α Jdx i)
            (Set.Icc (0 : ℝ) T ×ˢ Bc) q‖ ≤ v n i := by
    intro n hn
    have hspec := Classical.choose_spec (hmajorant n hn)
    have hveq : v n = Classical.choose (hmajorant n hn) := by
      rw [hv_def]; exact dif_pos hn
    rw [hveq]
    exact hspec
  have htsum_Bc : ContDiffOn ℝ (kk : ℕ)
      (fun q : ℝ × E => ∑' i, eigenRawIncrementMode (I := I) (M := M) g φ α Jdx i q)
      (Set.Icc (0 : ℝ) T ×ˢ Bc) := by
    have h := DifferentialGeometry.Analysis.contDiffOn_tsum (v := v) (x₀ := ((0 : ℝ), y₀))
      (N := (kk : ℕ∞))
      huniq hconv
      (fun i => ((eigenRawIncrementMode_contDiffOn_ofOrder (I := I) (M := M) (T := T)
        g kk φ hφ_smooth α Jdx i).mono
          (Set.prod_mono (le_refl _) hBc_sub)).of_le (by exact_mod_cast le_rfl))
      (fun n hn => (hv_spec n (by exact_mod_cast hn)).1)
      (fun n i q hq hn => (hv_spec n (by exact_mod_cast hn)).2 i q hq)
      ⟨Set.left_mem_Icc.mpr hT.le, Metric.mem_closedBall_self (by positivity)⟩
    exact h.of_le (by exact_mod_cast le_rfl)
  have htsum : ContDiffOn ℝ (kk : ℕ)
      (fun q : ℝ × E => ∑' i, eigenRawIncrementMode (I := I) (M := M) g φ α Jdx i q)
      (Set.Icc (0 : ℝ) T ×ˢ B) :=
    htsum_Bc.mono (Set.prod_mono (le_refl _) hball_le)
  refine htsum.congr ?_
  intro q hq
  have hq_symm_src : (extChartAt I α).symm q.2 ∈ (chartAt H α).source := by
    have hqt : q.2 ∈ (extChartAt I α).target := interior_subset (hB_sub hq.2)
    have := (extChartAt I α).map_target hqt
    rwa [extChartAt_source (I := I)] at this
  exact smoothCcTensor_rawChartComponent_eigenSeries_tsum_eq_local (I := I) (M := M)
    g (T_rep q.1) (fun i => φ i q.1) (hcoeff q.1 hq.1)
    (fun σ hσ => by
      obtain ⟨B', hB'_sum, hB'_le⟩ := hmodemass 0 (Nat.zero_le kk) σ hσ
      refine ⟨B', hB'_sum, fun i => ?_⟩
      have h := hB'_le i q.1 hq.1
      rwa [iteratedDeriv_zero] at h)
    α Jdx hq_symm_src

set_option maxHeartbeats 1600000 in
private theorem spectralPathFO_rawChartComponent_jointContMDiffOn_local
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (kk : ℕ)
      (fun p : M × ℝ =>
        tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep p.2) α ![] Jdx p.1)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
  set G : ℝ × E → ℝ :=
    fun q : ℝ × E => tensorChartComponentOnModel (I := I) (M := M) g (T_rep q.1) α Jdx q.2 with hG_def
  have hGEuclid : ContDiffOn ℝ (kk : ℕ) G
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    spectralPathFO_rawCompOnE_euclidean_contDiffOn_local (I := I) (M := M)
      g hT kk T_rep φ hφ_smooth hcoeff hmodemass α Jdx
  set f : M × ℝ → ℝ × E := fun p : M × ℝ => (p.2, extChartAt I α p.1) with hf_def
  have hf_smooth : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × E) (kk : ℕ) f
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    refine ContMDiffOn.prodMk_space contMDiffOn_snd ?_
    refine ((contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)).comp contMDiffOn_fst
      (fun p hp => hp.1)).of_le (by exact_mod_cast le_top)
  have hmaps : Set.MapsTo f ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    refine ⟨ht, ?_⟩
    have hx' : x ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source hx'
  have heq : Set.EqOn
      (fun p : M × ℝ =>
        tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep p.2) α ![] Jdx p.1)
      (G ∘ f)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    rintro ⟨x, t⟩ ⟨hx, _⟩
    have hx' : x ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
    simp only [Function.comp, hG_def, hf_def]
    have hraw : tensorChartComponentOnModel (I := I) (M := M) g (T_rep t) α Jdx (extChartAt I α x) =
        tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep t) α ![] Jdx
          ((extChartAt I α).symm (extChartAt I α x)) := rfl
    rw [hraw, (extChartAt I α).left_inv hx']
  intro q hq
  refine (ContMDiffWithinAt.congr ?_ (fun y hy => heq hy) (heq hq))
  have hGf : ContDiffWithinAt ℝ (kk : ℕ) G
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) (f q) :=
    hGEuclid.contDiffWithinAt (hmaps hq)
  exact hGf.comp_contMDiffWithinAt (hf_smooth q hq) hmaps

private theorem spectralPathFO_rawChartComponent_fibre_contDiffWithinAt_local
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (chartAt H α).source) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ContDiffWithinAt ℝ (kk : ℕ)
      (fun s : ℝ => tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep s) α ![] Jdx x)
      (Set.Icc (0 : ℝ) T) t := by
  have hCR := spectralPathFO_rawChartComponent_jointContMDiffOn_local (I := I) (M := M)
    g hT kk T_rep φ hφ_smooth hcoeff hmodemass α Jdx
  have harg : ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (kk : ℕ) (fun u : ℝ => (x, u))
      (Set.Icc (0 : ℝ) T) :=
    (contMDiffOn_const (c := x)).prodMk contMDiffOn_id
  have hmaps : Set.MapsTo (fun u : ℝ => (x, u)) (Set.Icc (0 : ℝ) T)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := fun u hu => ⟨hx, hu⟩
  have hcomp := hCR.comp harg hmaps
  rw [contMDiffOn_iff_contDiffOn] at hcomp
  exact hcomp t ht

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem spectralPathFO_section_jointContMDiffOn_local
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E))
      ((kk : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z) p.1
        ((T_rep p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) := by
  classical
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) 0 2
  refine contMDiffOn_of_locally_contMDiffOn ?_
  rintro ⟨x₀, s₀⟩ ⟨-, hs₀⟩
  refine ⟨(chartAt H x₀).source ×ˢ (Set.univ : Set ℝ),
    (chartAt H x₀).open_source.prod isOpen_univ,
    ⟨mem_chart_source H x₀, Set.mem_univ _⟩, ?_⟩
  set α : M := x₀ with hα
  have hsub_eq : ((Set.univ : Set M) ×ˢ Set.Icc (0 : ℝ) T) ∩
      ((chartAt H x₀).source ×ˢ (Set.univ : Set ℝ)) =
      (chartAt H x₀).source ×ˢ Set.Icc (0 : ℝ) T := by
    ext ⟨y, u⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, and_true]
    tauto
  rw [hsub_eq]
  have hSum : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      ((kk : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ => ∑ Q : CompIdx E 0 2,
        tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep p.2) α Q.1 Q.2 p.1 •
          tensorChartBasisElement (E := E) 0 2 Q.1 Q.2)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) := by
    refine contMDiffOn_finset_sum (fun Q _ => ?_)
    have hQ1 : Q.1 = (![] : Fin 0 → Fin (Module.finrank ℝ E)) := funext fun i0 => i0.elim0
    have hraw := spectralPathFO_rawChartComponent_jointContMDiffOn_local (I := I) (M := M)
      g hT kk T_rep φ hφ_smooth hcoeff hmodemass α Q.2
    rw [hQ1]
    exact hraw.smul contMDiffOn_const
  intro p₀ hp₀
  obtain ⟨hx₀src, hs₀'⟩ := hp₀
  have hbaseSet : p₀.1 ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
    change p₀.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
        ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
    refine ⟨?_, ?_⟩ <;>
      · change p₀.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
        rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
          TangentBundle.trivializationAt_baseSet (I := I) α]
        rw [hα]; exact hx₀src
  have hsource : (⟨p₀.1, (T_rep p₀.2).toSection p₀.1⟩ :
      TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)) ∈
      (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).source := by
    rw [Bundle.Trivialization.mem_source]; exact hbaseSet
  have hfibeq : ∀ p : M × ℝ, p.1 ∈ (chartAt H α).source →
      ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
        ⟨p.1, (T_rep p.2).toSection p.1⟩).2 =
        ∑ Q : CompIdx E 0 2,
          tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep p.2) α Q.1 Q.2 p.1 •
            tensorChartBasisElement (E := E) 0 2 Q.1 Q.2 := by
    intro p hpx
    have hpbase : p.1 ∈ (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).baseSet := by
      change p.1 ∈ ((trivializationAt (Tensor0SBundle.Tensor0SModel 0 ℝ E)
          (fun y : M => Tensor0SBundle.Tensor0SSpace 0 I y) α).baseSet) ∩
          ((trivializationAt (Tensor0SBundle.Tensor0SModel 2 ℝ E)
            (fun y : M => Tensor0SBundle.Tensor0SSpace 2 I y) α).baseSet)
      refine ⟨?_, ?_⟩ <;>
        · change p.1 ∈ (trivializationAt E (TangentSpace I) α).baseSet
          rw [show (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source from
            TangentBundle.trivializationAt_baseSet (I := I) α]
          exact hpx
    have h1 : ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
        ⟨p.1, (T_rep p.2).toSection p.1⟩).2 =
        (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).continuousLinearMapAt
          ℝ p.1 ((T_rep p.2).toSection p.1) := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply,
        Bundle.Trivialization.coe_linearMapAt_of_mem _ hpbase]
    rw [h1, toSection_eq_sum_chartBasisFiberSection (I := I) (M := M) g 0 2 (T_rep p.2) α hpx,
      map_sum]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [map_smul]
    congr 1
    have hbs : chartBasisFiberSection (I := I) (M := M) 0 2 α Q p.1 =
        (trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α).symmL ℝ p.1
          (tensorChartBasisElement (E := E) 0 2 Q.1 Q.2) := rfl
    rw [hbs]
    exact Bundle.Trivialization.continuousLinearMapAt_symmL _ hpbase _
  have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Tensor0SBundle.TensorRSModel 0 2 ℝ E) ((kk : ℕ) : WithTop ℕ∞)
      (fun p : M × ℝ =>
        ((trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
            (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α)
          ⟨p.1, (T_rep p.2).toSection p.1⟩).2)
      ((chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) p₀ := by
    refine (hSum p₀ ⟨hx₀src, hs₀'⟩).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact hfibeq p hp.1
    · exact hfibeq p₀ hx₀src
  exact ((Bundle.Trivialization.contMDiffWithinAt_iff
    (IM := I.prod 𝓘(ℝ, ℝ)) (n := ((kk : ℕ) : WithTop ℕ∞))
    (f := fun p : M × ℝ => (⟨p.1, (T_rep p.2).toSection p.1⟩ :
      TotalSpace (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
        (fun z : M => Tensor0SBundle.TensorRSSpace 0 2 I z)))
    (s := (chartAt H α).source ×ˢ Set.Icc (0 : ℝ) T) (x₀ := p₀)
    (e := trivializationAt (Tensor0SBundle.TensorRSModel 0 2 ℝ E)
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) α) hsource).mpr
    ⟨contMDiffWithinAt_fst, hfib⟩)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem spectralPathFO_toFun_timeJet_eq_of_coeff_jets_local
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ B i)
    (j : ℕ) (hj : j ≤ kk) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (Rt : SmoothCcTensor g 0 2)
    (hRt : ∀ i, tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) Rt) i = iteratedDeriv j (φ i) t)
    (x : M) :
    Rt.toFun x =
      iteratedDerivWithin j (fun s => (T_rep s).toFun x) (Set.Icc (0 : ℝ) T) t := by
  classical
  set α : M := x with hα
  have hx : x ∈ (chartAt H α).source := mem_chart_source H x
  have hUD : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T) := uniqueDiffOn_Icc hT
  have hjm : ∀ σ : ℝ, 0 ≤ σ →
      ∃ B : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable B ∧
        ∀ i, tensorSobolevWeight (I := I) (M := M) i σ *
            (iteratedDeriv j (φ i) t) ^ 2 ≤ B i := by
    intro σ hσ
    obtain ⟨B, hB1, hB2⟩ := hmodemass j hj σ hσ
    exact ⟨B, hB1, fun i => hB2 i t ht⟩
  set w : CompIdx E 0 2 → Tensor0SBundle.TensorRSModel 0 2 ℝ E := fun Q =>
    Tensor0SBundle.TensorRSSpace.toModel
      (chartBasisFiberSection (I := I) (M := M) 0 2 α Q x) with hw_def
  set A : (CompIdx E 0 2 → ℝ) →L[ℝ] Tensor0SBundle.TensorRSModel 0 2 ℝ E :=
    ∑ Q : CompIdx E 0 2, (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : CompIdx E 0 2 => ℝ) Q).smulRight (w Q) with hA_def
  have hAapply : ∀ c : CompIdx E 0 2 → ℝ, A c = ∑ Q : CompIdx E 0 2, c Q • w Q := by
    intro c
    rw [hA_def, ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun Q _ => by
      rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply])
  have hexp : ∀ Z : SmoothCcTensor g 0 2,
      Z.toFun x = A (fun Q =>
        tensorChartComponentRaw (I := I) (M := M) g 0 2 Z α Q.1 Q.2 x) := by
    intro Z
    rw [hAapply]
    have h1 : Z.toFun x = Tensor0SBundle.TensorRSSpace.toModel (Z.toSection x) := rfl
    have h3 : ∀ v : Tensor0SBundle.TensorRSSpace 0 2 I x,
        Tensor0SBundle.TensorRSSpace.toModel v
          = Tensor0SBundle.TensorRSSpace.toModelL (𝕜 := ℝ) (I := I) 0 2 x v := fun v => rfl
    rw [h1, toSection_eq_sum_chartBasisFiberSection (I := I) (M := M) g 0 2 Z α hx,
      h3, map_sum]
    exact Finset.sum_congr rfl (fun Q _ => by rw [map_smul, ← h3, hw_def])
  set rawγ : ℝ → CompIdx E 0 2 → ℝ := fun s Q =>
    tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep s) α Q.1 Q.2 x with hrawγ_def
  have hγpath : (fun s => (T_rep s).toFun x) = fun s => A (rawγ s) :=
    funext fun s => hexp (T_rep s)
  have hQ1 : ∀ Q : CompIdx E 0 2, Q.1 = (![] : Fin 0 → Fin (Module.finrank ℝ E)) :=
    fun Q => funext fun i0 => i0.elim0
  have hraws : ∀ Q : CompIdx E 0 2, ContDiffWithinAt ℝ (j : ℕ)
      (fun s => rawγ s Q) (Set.Icc (0 : ℝ) T) t := by
    intro Q
    have h := spectralPathFO_rawChartComponent_fibre_contDiffWithinAt_local (I := I) (M := M)
      g hT kk T_rep φ hφ_smooth hcoeff hmodemass α Q.2 hx ht
    have hfun : (fun s => rawγ s Q) =
        (fun s : ℝ => tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep s) α ![]
          Q.2 x) := by
      funext s
      change tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep s) α Q.1 Q.2 x = _
      rw [hQ1 Q]
    rw [hfun]
    exact h.of_le (by exact_mod_cast hj)
  have hγvec : ContDiffWithinAt ℝ (j : ℕ) rawγ (Set.Icc (0 : ℝ) T) t :=
    contDiffWithinAt_pi.2 hraws
  have hstep1 : iteratedDerivWithin j (fun s => (T_rep s).toFun x) (Set.Icc (0 : ℝ) T) t
      = A (iteratedDerivWithin j rawγ (Set.Icc (0 : ℝ) T) t) := by
    rw [hγpath]
    exact clm_comm_iteratedDerivWithin_finiteOrder A rawγ hT ht j hγvec
  have hstep2 : iteratedDerivWithin j rawγ (Set.Icc (0 : ℝ) T) t
      = fun Q => iteratedDerivWithin j (fun s => rawγ s Q) (Set.Icc (0 : ℝ) T) t := by
    funext Q
    have hproj := clm_comm_iteratedDerivWithin_finiteOrder
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : CompIdx E 0 2 => ℝ) Q)
      rawγ hT ht j hγvec
    simp only [ContinuousLinearMap.proj_apply] at hproj
    exact hproj.symm
  have hstep3 : ∀ Q : CompIdx E 0 2,
      iteratedDerivWithin j (fun s => rawγ s Q) (Set.Icc (0 : ℝ) T) t
        = ∑' i, iteratedDeriv j (φ i) t *
            tensorChartComponentRaw (I := I) (M := M) g 0 2
              (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Q.2 x := by
    intro Q
    obtain ⟨CK, pK, hCK_nn, hCK⟩ :=
      exists_rawComponentRaw_eigen_pointwise_le_lambda_pow (I := I) (M := M) g α Q.2 hx
    set K : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ := fun i =>
      tensorChartComponentRaw (I := I) (M := M) g 0 2
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Q.2 x with hK_def
    set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
    have hsW_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < (sW : ℝ) := by
      rw [hsW_def]; push_cast; linarith
    set σ0 : ℝ := 2 * ((pK : ℝ) + (sW : ℝ)) with hσ0_def
    have hσ0_nn : (0 : ℝ) ≤ σ0 := by rw [hσ0_def]; positivity
    have hbase_pos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
        (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
      have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
    have hcollapse : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pK : ℝ) + (sW : ℝ)))
          * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (pK : ℕ)
          = tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) := by
      intro i
      unfold tensorSobolevWeight
      rw [← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) pK,
        ← Real.rpow_add (hbase_pos i)]
      congr 1; ring
    have htimeC : ∀ a : ℕ, ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ,
        a ≤ kk → Summable Cm ∧
          ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) T,
            tensorSobolevWeight (I := I) (M := M) i σ0 *
              (iteratedDeriv a (φ i) s) ^ 2 ≤ Cm i := by
      intro a
      by_cases ha : a ≤ kk
      · obtain ⟨Cm, h1, h2⟩ := hmodemass a ha σ0 hσ0_nn
        exact ⟨Cm, fun _ => ⟨h1, h2⟩⟩
      · exact ⟨fun _ => 0, fun h => absurd h ha⟩
    choose Cmf hCmf using htimeC
    have hCm_nn : ∀ (a : ℕ), a ≤ kk →
        ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), 0 ≤ Cmf a i := by
      intro a ha i
      have h := (hCmf a ha).2 i 0 (Set.left_mem_Icc.mpr hT.le)
      have hw := tensorSobolevWeight_pos (I := I) (M := M) i σ0
      nlinarith [sq_nonneg (iteratedDeriv a (φ i) 0), hw.le, h]
    set v : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ := fun a i =>
      if a ≤ kk then CK * (Real.sqrt (Cmf a i) *
        tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) else 0 with hv_def
    have hveq : ∀ (a : ℕ), a ≤ kk → v a = fun i => CK * (Real.sqrt (Cmf a i) *
        tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
      intro a ha
      funext i
      change (if a ≤ kk then CK * (Real.sqrt (Cmf a i) *
        tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) else 0) = _
      rw [if_pos ha]
    have hv_sum : ∀ a : ℕ, a ≤ kk → Summable (v a) := by
      intro a ha
      rw [hveq a ha]
      exact Summable.mul_left CK (summable_sqrt_mul_weight_neg (I := I) (M := M) g
        (Cmf a) (hCmf a ha).1 (hCm_nn a ha) hsW_gt)
    have hterm_bound : ∀ (a : ℕ), a ≤ kk →
        ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ s ∈ Set.Icc (0 : ℝ) T,
        ‖iteratedFDerivWithin ℝ a (fun u : ℝ => φ i u * K i) (Set.Icc (0 : ℝ) T) s‖
          ≤ v a i := by
      intro a ha i s hs
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
        iteratedDerivWithin_mul_const_field, Real.norm_eq_abs, abs_mul]
      have hwithin : iteratedDerivWithin a (φ i) (Set.Icc (0 : ℝ) T) s
          = iteratedDeriv a (φ i) s :=
        iteratedDerivWithin_eq_iteratedDeriv hUD
          ((hφ_smooth i).contDiffAt.of_le (by exact_mod_cast ha)) hs
      rw [hwithin]
      have hmass_s : tensorSobolevWeight (I := I) (M := M) i
          (2 * ((pK : ℝ) + (sW : ℝ))) * (iteratedDeriv a (φ i) s) ^ 2 ≤ Cmf a i := by
        have h := (hCmf a ha).2 i s hs
        rwa [hσ0_def] at h
      have hφ_le := abs_le_sqrt_of_weight_sq_le (I := I) (M := M) g i
        ((pK : ℝ) + (sW : ℝ)) hmass_s
      have hK_le := hCK i
      have hva : v a i = CK * (Real.sqrt (Cmf a i) *
          tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by
        rw [hveq a ha]
      rw [hva, ← hcollapse i]
      calc |iteratedDeriv a (φ i) s| * |K i|
          ≤ (Real.sqrt (Cmf a i) *
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pK : ℝ) + (sW : ℝ)))) *
            (CK * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pK) := by
            refine mul_le_mul hφ_le ?_ (abs_nonneg _) ?_
            · rw [hK_def]; exact hK_le
            · exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (hbase_pos i).le _)
        _ = CK * (Real.sqrt (Cmf a i) *
              ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pK : ℝ) + (sW : ℝ)))
                * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (pK : ℕ))) := by ring
    have hfterms : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
        ContDiffOn ℝ ((kk : ℕ∞)) (fun u : ℝ => φ i u * K i) (Set.Icc (0 : ℝ) T) :=
      fun i => (((hφ_smooth i).mul contDiff_const).contDiffOn).of_le
        (by exact_mod_cast le_rfl)
    have hEq : ∀ s ∈ Set.Icc (0 : ℝ) T, rawγ s Q = ∑' i, φ i s * K i := by
      intro s hs
      have hfun : rawγ s Q =
          tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep s) α ![] Q.2 x := by
        change tensorChartComponentRaw (I := I) (M := M) g 0 2 (T_rep s) α Q.1 Q.2 x = _
        rw [hQ1 Q]
      rw [hfun]
      exact smoothCcTensor_rawChartComponent_eigenSeries_tsum_eq_local (I := I) (M := M)
        g (T_rep s) (fun i => φ i s) (hcoeff s hs)
        (fun σ hσ => by
          obtain ⟨B', hB'_sum, hB'_le⟩ := hmodemass 0 (Nat.zero_le kk) σ hσ
          refine ⟨B', hB'_sum, fun i => ?_⟩
          have h := hB'_le i s hs
          rwa [iteratedDeriv_zero] at h)
        α Q.2 hx
    rw [iteratedDerivWithin_congr hEq ht]
    have hFD := DifferentialGeometry.Analysis.iteratedFDerivWithin_tsum
      (f := fun (i : TensorEigenIdx (I := I) (M := M) g 0 2) (u : ℝ) => φ i u * K i)
      (v := v) (s := Set.Icc (0 : ℝ) T) (N := (kk : ℕ∞))
      hUD (convex_Icc 0 T) hfterms
      (fun a ha => hv_sum a (by exact_mod_cast ha))
      (fun a i s hs ha => hterm_bound a (by exact_mod_cast ha) i s hs)
      (Set.left_mem_Icc.mpr hT.le) (k := j) (by exact_mod_cast hj) ht
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin, hFD]
    have hsumFD : Summable (fun i => iteratedFDerivWithin ℝ j
        (fun u : ℝ => φ i u * K i) (Set.Icc (0 : ℝ) T) t) :=
      Summable.of_norm_bounded (hv_sum j hj) (fun i => hterm_bound j hj i t ht)
    have happly := ContinuousLinearMap.map_tsum
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℝ) ℝ (fun _ => (1 : ℝ))) hsumFD
    have happly' : (∑' i, iteratedFDerivWithin ℝ j (fun u : ℝ => φ i u * K i)
        (Set.Icc (0 : ℝ) T) t) (fun _ => (1 : ℝ))
        = ∑' i, (iteratedFDerivWithin ℝ j (fun u : ℝ => φ i u * K i)
          (Set.Icc (0 : ℝ) T) t) (fun _ => (1 : ℝ)) := happly
    rw [happly']
    refine tsum_congr (fun i => ?_)
    rw [← iteratedDerivWithin_eq_iteratedFDerivWithin,
      iteratedDerivWithin_mul_const_field,
      iteratedDerivWithin_eq_iteratedDeriv hUD
        ((hφ_smooth i).contDiffAt.of_le (by exact_mod_cast hj)) ht]
  have hRt_exp : ∀ Q : CompIdx E 0 2,
      tensorChartComponentRaw (I := I) (M := M) g 0 2 Rt α Q.1 Q.2 x
        = ∑' i, iteratedDeriv j (φ i) t *
            tensorChartComponentRaw (I := I) (M := M) g 0 2
              (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Q.2 x := by
    intro Q
    rw [hQ1 Q]
    exact smoothCcTensor_rawChartComponent_eigenSeries_tsum_eq_local (I := I) (M := M)
      g Rt (fun i => iteratedDeriv j (φ i) t) hRt hjm α Q.2 hx
  calc Rt.toFun x
      = A (fun Q => tensorChartComponentRaw (I := I) (M := M) g 0 2 Rt α Q.1 Q.2 x) :=
        hexp Rt
    _ = A (fun Q => iteratedDerivWithin j (fun s => rawγ s Q) (Set.Icc (0 : ℝ) T) t) := by
        congr 1
        funext Q
        rw [hRt_exp Q, ← hstep3 Q]
    _ = A (iteratedDerivWithin j rawγ (Set.Icc (0 : ℝ) T) t) := by
        congr 1
        exact hstep2.symm
    _ = iteratedDerivWithin j (fun s => (T_rep s).toFun x) (Set.Icc (0 : ℝ) T) t :=
        hstep1.symm

end FiniteOrderSpectralPathEngine

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
