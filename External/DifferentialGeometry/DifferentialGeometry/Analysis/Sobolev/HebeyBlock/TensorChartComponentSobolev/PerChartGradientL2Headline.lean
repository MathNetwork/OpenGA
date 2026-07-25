import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChristoffelCorrectionL2.FiberNormGradientDecomp
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChristoffelCorrectionL2.IntrinsicCovAtomL2Fiber
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChristoffelCorrectionL2.IntrinsicSlotOpNormRiem
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorComponentGradientEpNormPerAlpha


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HebeyBlock

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Tensor.TensorRSRiemannianBundle
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma a3_pouTsupport_isCompact (α : M) :
    IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).isCompact

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma a3_pouTsupport_subset_chartSource (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H α).source :=
  chartAtlasPOU_isSubordinate (I := I) (M := M) α

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartTensorRSCovariantDerivative_totalSpace_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s) (k : Fin (Module.finrank ℝ E)) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ContinuousOn
      (fun b : M =>
        (TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun y : M => TensorRSSpace r s I y) b
          (chartTensorRSCovariantDerivative (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α k) b) :
          TotalSpace (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y)))
      (chartAt H α).source := by
  classical
  have hbase_eq :
      (trivializationAt E (TangentSpace I) α).baseSet =
        (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  have hsmooth :=
    tensorCovDeriv_chartBasis_contMDiffOn (I := I) (M := M) g r s
      S.toCcTensor α k
  have hcont :
      ContinuousOn
        (fun b : M =>
          (TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun y : M => TensorRSSpace r s I y) b
            (tensorCovDerivAt (I := I) (M := M) g r s S.toCcTensor b
              (chartBasisVecFiber (I := I) α k b)) :
            TotalSpace (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    hsmooth.continuousOn
  rw [hbase_eq] at hcont
  refine hcont.congr ?_
  intro b hb
  have hcov_eq :=
    chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at
      (I := I) (M := M) g r s α S.toCcTensor (chartBasisVecFiber (I := I) α k) hb
  simp only [hcov_eq]

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartTensorRSCovariantDerivative_pouWeightedNorm_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    AEStronglyMeasurable
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α k) b‖ ^ 2))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  set ρ : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hρ_def
  set f : M → ℝ := fun b : M =>
    ρ b *
      Real.sqrt
        (∑ k : Fin (Module.finrank ℝ E),
          ‖chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (chartBasisVecFiber (I := I) α k) b‖ ^ 2) with hf_def
  have h_indicator_eq :
      f = (tsupport ρ).indicator f := by
    funext b
    by_cases hb : b ∈ tsupport ρ
    · rw [Set.indicator_of_mem hb]
    · rw [Set.indicator_of_notMem hb]
      have hρ_zero : ρ b = 0 := by
        by_contra hne
        exact hb (subset_tsupport _ hne)
      rw [hf_def]; simp only [hρ_zero, zero_mul]
  have h_meas : MeasurableSet (tsupport ρ) :=
    (isClosed_tsupport _).measurableSet
  rw [h_indicator_eq, aestronglyMeasurable_indicator_iff h_meas]
  refine ContinuousOn.aestronglyMeasurable_of_isCompact ?_
    (a3_pouTsupport_isCompact (I := I) (M := M) α)
    h_meas
  have hsub : tsupport ρ ⊆ (chartAt H α).source :=
    a3_pouTsupport_subset_chartSource (I := I) (M := M) α
  have h_pou_on : ContinuousOn ρ (tsupport ρ) := by
    rw [hρ_def]
    exact ((chartAtlasPOU I M α).contMDiff.continuous).continuousOn
  have h_sumsq : ContinuousOn
      (fun b : M =>
        ∑ k : Fin (Module.finrank ℝ E),
          ‖chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (chartBasisVecFiber (I := I) α k) b‖ ^ 2)
      (chartAt H α).source := by
    refine continuousOn_finset_sum _ (fun k _ => ?_)
    have h_inner : ContinuousOn
        (fun b : M =>
          (⟪chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (chartBasisVecFiber (I := I) α k) b,
            chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (chartBasisVecFiber (I := I) α k) b⟫_ℝ : ℝ))
        (chartAt H α).source :=
      ContinuousOn.inner_bundle
        (chartTensorRSCovariantDerivative_totalSpace_continuousOn (I := I) (M := M) g r s α S k)
        (chartTensorRSCovariantDerivative_totalSpace_continuousOn (I := I) (M := M) g r s α S k)
    refine h_inner.congr ?_
    intro b _
    exact (real_inner_self_eq_norm_sq _).symm
  have h_sqrt : ContinuousOn
      (fun b : M =>
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            ‖chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (chartBasisVecFiber (I := I) α k) b‖ ^ 2))
      (chartAt H α).source :=
    Real.continuous_sqrt.comp_continuousOn h_sumsq
  exact h_pou_on.mul (h_sqrt.mono hsub)

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartTensorRSSlotCorrection_norm_sq_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s) (k : Fin (Module.finrank ℝ E)) (b : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ‖- (∑ i : Fin r,
          chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α k) b i)
      + (∑ l : Fin s,
          chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α k) b l)‖ ^ 2 ≤
      (2 * ((r : ℝ) + (s : ℝ))) *
        ((∑ i : Fin r,
            ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (chartBasisVecFiber (I := I) α k) b i‖ ^ 2) +
          (∑ l : Fin s,
            ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (chartBasisVecFiber (I := I) α k) b l‖ ^ 2)) := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  set a : Fin r → TensorRSSpace r s I b := fun i =>
    chartTensorRSInputSlotCorrection (I := I) r s g α
      (fun b' => S.toCcTensor.toSection b') (chartBasisVecFiber (I := I) α k) b i
    with ha_def
  set c : Fin s → TensorRSSpace r s I b := fun l =>
    chartTensorRSOutputSlotCorrection (I := I) r s g α
      (fun b' => S.toCcTensor.toSection b') (chartBasisVecFiber (I := I) α k) b l
    with hc_def
  have h_a_sum_nn : 0 ≤ ∑ i : Fin r, ‖a i‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_c_sum_nn : 0 ≤ ∑ l : Fin s, ‖c l‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_split :
      ‖- (∑ i : Fin r, a i) + (∑ l : Fin s, c l)‖ ^ 2 ≤
        2 * (‖∑ i : Fin r, a i‖ ^ 2 + ‖∑ l : Fin s, c l‖ ^ 2) := by
    set u : TensorRSSpace r s I b := ∑ i : Fin r, a i with hu_def
    set v : TensorRSSpace r s I b := ∑ l : Fin s, c l with hv_def
    have h_tri : ‖- u + v‖ ≤ ‖u‖ + ‖v‖ := by
      calc ‖- u + v‖ ≤ ‖- u‖ + ‖v‖ := norm_add_le _ _
        _ = ‖u‖ + ‖v‖ := by rw [norm_neg]
    have h_lhs_nn : 0 ≤ ‖- u + v‖ := norm_nonneg _
    have h_sq : ‖- u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
      have := mul_self_le_mul_self h_lhs_nn h_tri
      rw [← sq, ← sq] at this; exact this
    have h_abc : (‖u‖ + ‖v‖) ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      have h_diff_nn : 0 ≤ (‖u‖ - ‖v‖) ^ 2 := sq_nonneg _
      nlinarith [h_diff_nn]
    exact h_sq.trans h_abc
  have h_u_pm : ‖∑ i : Fin r, a i‖ ^ 2 ≤ (r : ℝ) * ∑ i : Fin r, ‖a i‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin r)))
      (f := fun i => ‖a i‖)
    have h_tri : ‖∑ i : Fin r, a i‖ ≤ ∑ i : Fin r, ‖a i‖ := norm_sum_le _ _
    have h_sq_tri : ‖∑ i : Fin r, a i‖ ^ 2 ≤ (∑ i : Fin r, ‖a i‖) ^ 2 := by
      have := mul_self_le_mul_self (norm_nonneg _) h_tri
      rw [← sq, ← sq] at this; exact this
    refine h_sq_tri.trans ?_
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have h_v_pm : ‖∑ l : Fin s, c l‖ ^ 2 ≤ (s : ℝ) * ∑ l : Fin s, ‖c l‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin s)))
      (f := fun l => ‖c l‖)
    have h_tri : ‖∑ l : Fin s, c l‖ ≤ ∑ l : Fin s, ‖c l‖ := norm_sum_le _ _
    have h_sq_tri : ‖∑ l : Fin s, c l‖ ^ 2 ≤ (∑ l : Fin s, ‖c l‖) ^ 2 := by
      have := mul_self_le_mul_self (norm_nonneg _) h_tri
      rw [← sq, ← sq] at this; exact this
    refine h_sq_tri.trans ?_
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have h_r_le : (r : ℝ) ≤ (r : ℝ) + (s : ℝ) := by
    have : (0 : ℝ) ≤ (s : ℝ) := by positivity
    linarith
  have h_s_le : (s : ℝ) ≤ (r : ℝ) + (s : ℝ) := by
    have : (0 : ℝ) ≤ (r : ℝ) := by positivity
    linarith
  calc ‖- (∑ i : Fin r, a i) + (∑ l : Fin s, c l)‖ ^ 2
      ≤ 2 * (‖∑ i : Fin r, a i‖ ^ 2 + ‖∑ l : Fin s, c l‖ ^ 2) := h_split
    _ ≤ 2 * ((r : ℝ) * (∑ i : Fin r, ‖a i‖ ^ 2)
          + (s : ℝ) * (∑ l : Fin s, ‖c l‖ ^ 2)) := by
        have := add_le_add h_u_pm h_v_pm; linarith
    _ ≤ (2 * ((r : ℝ) + (s : ℝ))) *
          ((∑ i : Fin r, ‖a i‖ ^ 2) + (∑ l : Fin s, ‖c l‖ ^ 2)) := by
        have h1 : (r : ℝ) * (∑ i : Fin r, ‖a i‖ ^ 2) ≤
            ((r : ℝ) + (s : ℝ)) * (∑ i : Fin r, ‖a i‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h_r_le h_a_sum_nn
        have h2 : (s : ℝ) * (∑ l : Fin s, ‖c l‖ ^ 2) ≤
            ((r : ℝ) + (s : ℝ)) * (∑ l : Fin s, ‖c l‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h_s_le h_c_sum_nn
        nlinarith [h1, h2]

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [CompleteSpace E] in
theorem exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (fun b : M => Real.sqrt
            (g.inner b
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b)
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b))) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨A, B, hA_nn, hB_nn, h_G1⟩ :=
    g_inner_gradFun_le_pou_weighted_fiber_norm_atoms_on_pouTsupport_h1
      (I := I) (M := M) g r s α
  set C_bridge : ℝ := 2 * ((r : ℝ) + (s : ℝ)) with hC_bridge_def
  have hC_bridge_nn : 0 ≤ C_bridge := by rw [hC_bridge_def]; positivity
  obtain ⟨C₂, hC₂_nn, h_G2⟩ :=
    exists_eLpNorm_pou_mul_sum_fiber_chart_cov_le_const_mul_h1Norm
      (I := I) (M := M) g r s α
  obtain ⟨C₄, hC₄_nn, h_G4⟩ :=
    exists_integral_indicator_tsupp_raw_sq_le_const_mul_h1NormSq
      (I := I) (M := M) g r s α
  obtain ⟨M_F_in, hM_F_in_nn, hM_F_in_le⟩ :=
    chartTensorRSInputSlotCorrection_riemannian_norm_le_on_pouTsupport
      (I := I) (M := M) g r s α
  obtain ⟨M_F_out, hM_F_out_nn, hM_F_out_le⟩ :=
    chartTensorRSOutputSlotCorrection_riemannian_norm_le_on_pouTsupport
      (I := I) (M := M) g r s α
  set M_F : ℝ := max M_F_in M_F_out with hM_F_def
  have hM_F_nn : 0 ≤ M_F := le_max_of_le_left hM_F_in_nn
  set n : ℕ := Module.finrank ℝ E with hn_def
  set C₃ : ℝ := B * C_bridge * (n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2 with hC₃_def
  have hC₃_nn : 0 ≤ C₃ := by rw [hC₃_def]; positivity
  set C_sq : ℝ := A * C₄ ^ 2 + B * C₂ ^ 2 + C₃ with hC_sq_def
  have hC_sq_nn : 0 ≤ C_sq := by rw [hC_sq_def]; positivity
  set C : ℝ := Real.sqrt C_sq with hC_def
  have hC_nn : 0 ≤ C := Real.sqrt_nonneg _
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g
    with hμ_def
  set u : M → ℝ := tensorChartComponentScalar (I := I) (M := M)
      g r s S.toCcTensor α Idx Jdx with hu_def
  set ρ : M → ℝ := fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hρ_def
  set Tinner : M → ℝ := fun b : M =>
      g.inner b (gradFun (I := I) g u b) (gradFun (I := I) g u b)
    with hTinner_def
  set TinnerSqrt : M → ℝ := fun b : M => Real.sqrt (Tinner b) with hTinnerSqrt_def
  have hTinner_nn : ∀ b, 0 ≤ Tinner b := fun b => by
    rw [hTinner_def]
    exact DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
      (I := I) (M := M) g b _
  change eLpNorm TinnerSqrt 2 μ ≤ ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞)
  set rawZ : M → ℝ := fun b : M =>
      scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M)
          g r s S.toCcTensor α Idx Jdx) (extChartAt I α b) with hrawZ_def
  set rawInd : M → ℝ := fun b : M =>
      (tsupport ρ).indicator rawZ b with hrawInd_def
  set Tcov : M → ℝ := fun b : M => ∑ k : Fin (Module.finrank ℝ E),
      ‖chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toCcTensor.toSection b')
          (chartBasisVecFiber (I := I) α k) b‖ ^ 2
    with hTcov_def
  set TchrPerK : Fin (Module.finrank ℝ E) → M → ℝ := fun k b =>
    (∑ i : Fin r,
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α k) b i‖ ^ 2) +
      (∑ l : Fin s,
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α k) b l‖ ^ 2)
    with hTchrPerK_def
  set TchrSumK : M → ℝ := fun b : M => ∑ k : Fin (Module.finrank ℝ E), TchrPerK k b
    with hTchrSumK_def
  set TchrFib : M → ℝ := fun b : M => ∑ k : Fin (Module.finrank ℝ E),
      ‖- (∑ i : Fin r,
            chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (chartBasisVecFiber (I := I) α k) b i)
        + (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (chartBasisVecFiber (I := I) α k) b l)‖ ^ 2
    with hTchrFib_def
  have hρ_nn : ∀ b, 0 ≤ ρ b := fun b => by
    rw [hρ_def]; exact (chartAtlasPOU I M).nonneg α b
  have h_ptbound : ∀ b : M, Tinner b ≤
      A * (rawInd b) ^ 2 +
        B * (ρ b) ^ 2 * Tcov b +
        B * C_bridge * (ρ b) ^ 2 * TchrSumK b := by
    intro b
    by_cases hb : b ∈ tsupport ρ
    · have h_G1' : Tinner b ≤
          A * rawZ b ^ 2 + B * (ρ b) ^ 2 * (Tcov b + TchrFib b) := h_G1 S Idx Jdx b hb
      have h_TchrFib_le : TchrFib b ≤ C_bridge * TchrSumK b := by
        rw [hTchrFib_def, hTchrSumK_def]
        have h1 : ∑ k : Fin (Module.finrank ℝ E),
            ‖- (∑ i : Fin r,
                  chartTensorRSInputSlotCorrection (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b i)
              + (∑ l : Fin s,
                  chartTensorRSOutputSlotCorrection (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b l)‖ ^ 2 ≤
            ∑ k : Fin (Module.finrank ℝ E), C_bridge * TchrPerK k b :=
          Finset.sum_le_sum (fun k _ => by
            rw [hTchrPerK_def, hC_bridge_def]
            exact chartTensorRSSlotCorrection_norm_sq_le (I := I) (M := M) g r s α S k b)
        rwa [← Finset.mul_sum] at h1
      have h_Tcov_nn : 0 ≤ Tcov b := by
        rw [hTcov_def]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have h_TchrSumK_nn : 0 ≤ TchrSumK b := by
        rw [hTchrSumK_def]
        refine Finset.sum_nonneg (fun k _ => ?_)
        rw [hTchrPerK_def]
        exact add_nonneg
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      have h_Bρ_sq_nn : 0 ≤ B * (ρ b) ^ 2 := mul_nonneg hB_nn (sq_nonneg _)
      have h_rawInd_eq : rawInd b = rawZ b := by
        change (tsupport ρ).indicator rawZ b = rawZ b
        exact Set.indicator_of_mem hb _
      have h_TchrFib_step : B * (ρ b) ^ 2 * TchrFib b ≤
          B * (ρ b) ^ 2 * (C_bridge * TchrSumK b) :=
        mul_le_mul_of_nonneg_left h_TchrFib_le h_Bρ_sq_nn
      calc Tinner b
          ≤ A * rawZ b ^ 2 + B * (ρ b) ^ 2 * (Tcov b + TchrFib b) := h_G1'
        _ = A * rawZ b ^ 2 + B * (ρ b) ^ 2 * Tcov b +
              B * (ρ b) ^ 2 * TchrFib b := by ring
        _ ≤ A * rawZ b ^ 2 + B * (ρ b) ^ 2 * Tcov b +
              B * (ρ b) ^ 2 * (C_bridge * TchrSumK b) := by linarith
        _ = A * rawInd b ^ 2 + B * (ρ b) ^ 2 * Tcov b +
              B * C_bridge * (ρ b) ^ 2 * TchrSumK b := by
              rw [h_rawInd_eq]; ring
    · have h_sqrt_zero :
          Real.sqrt (g.inner b
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx) b)
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx) b)) = 0 :=
        sqrt_g_inner_gradFun_tensorChartComponentScalar_eq_zero_outside_pouTsupport
          (I := I) (M := M) g r s S.toCcTensor α Idx Jdx hb
      have h_Tinner_zero : Tinner b = 0 := by
        rw [hTinner_def, hu_def]
        have h_nn := hTinner_nn b
        rw [hTinner_def, hu_def] at h_nn
        exact (Real.sqrt_eq_zero h_nn).mp h_sqrt_zero
      rw [h_Tinner_zero]
      have h_rawInd_zero : rawInd b = 0 := by
        change (tsupport ρ).indicator rawZ b = 0
        exact Set.indicator_of_notMem hb _
      have h_ρ_zero : ρ b = 0 := by
        by_contra hne
        exact hb (subset_tsupport _ hne)
      rw [h_rawInd_zero, h_ρ_zero]
      simp
  have h_TinnerSqrt_sq : ∀ b, (TinnerSqrt b) ^ 2 = Tinner b := fun b => by
    rw [hTinnerSqrt_def, Real.sq_sqrt (hTinner_nn b)]
  have h_pt_enn : ∀ b, (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (A * (rawInd b) ^ 2) +
        ENNReal.ofReal (B * (ρ b) ^ 2 * Tcov b) +
        ENNReal.ofReal (B * C_bridge * (ρ b) ^ 2 * TchrSumK b) := by
    intro b
    have h_lhs : (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (Tinner b) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
        sq_abs, h_TinnerSqrt_sq]
    rw [h_lhs]
    have h_t1_nn : 0 ≤ A * (rawInd b) ^ 2 := mul_nonneg hA_nn (sq_nonneg _)
    have h_Tcov_nn : 0 ≤ Tcov b := by
      rw [hTcov_def]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h_TchrSumK_nn : 0 ≤ TchrSumK b := by
      rw [hTchrSumK_def]
      refine Finset.sum_nonneg (fun k _ => ?_)
      rw [hTchrPerK_def]
      exact add_nonneg
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have h_t2_nn : 0 ≤ B * (ρ b) ^ 2 * Tcov b :=
      mul_nonneg (mul_nonneg hB_nn (sq_nonneg _)) h_Tcov_nn
    have h_t3_nn : 0 ≤ B * C_bridge * (ρ b) ^ 2 * TchrSumK b :=
      mul_nonneg (mul_nonneg (mul_nonneg hB_nn hC_bridge_nn) (sq_nonneg _))
        h_TchrSumK_nn
    have h_add :
        ENNReal.ofReal (A * (rawInd b) ^ 2 + B * (ρ b) ^ 2 * Tcov b +
            B * C_bridge * (ρ b) ^ 2 * TchrSumK b) =
          ENNReal.ofReal (A * (rawInd b) ^ 2) +
            ENNReal.ofReal (B * (ρ b) ^ 2 * Tcov b) +
            ENNReal.ofReal (B * C_bridge * (ρ b) ^ 2 * TchrSumK b) := by
      rw [ENNReal.ofReal_add (add_nonneg h_t1_nn h_t2_nn) h_t3_nn,
          ENNReal.ofReal_add h_t1_nn h_t2_nn]
    rw [← h_add]
    exact ENNReal.ofReal_le_ofReal (h_ptbound b)
  have h_sq_to_lint :
      (eLpNorm TinnerSqrt 2 μ) ^ 2 =
        ∫⁻ b, (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
    have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by
      show ENNReal.toReal 2 = 2; rfl
    rw [h2_toReal]
    have h_inner_eq : ∫⁻ b, (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
        ∫⁻ b, (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards with b
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
    rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
    norm_num
  have h_sq_bound : (eLpNorm TinnerSqrt 2 μ) ^ 2 ≤
      ENNReal.ofReal (C_sq * ‖S‖ ^ 2) := by
    rw [h_sq_to_lint]
    set f1 : M → ℝ≥0∞ := fun b => ENNReal.ofReal (A * (rawInd b) ^ 2) with hf1_def
    set f2 : M → ℝ≥0∞ :=
      fun b => ENNReal.ofReal (B * (ρ b) ^ 2 * Tcov b) with hf2_def
    set f3 : M → ℝ≥0∞ :=
      fun b => ENNReal.ofReal (B * C_bridge * (ρ b) ^ 2 * TchrSumK b) with hf3_def
    have h_lint_mono :
        ∫⁻ b, (‖TinnerSqrt b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
          ∫⁻ b, f1 b + f2 b + f3 b ∂μ := by
      refine lintegral_mono_ae ?_
      filter_upwards with b using h_pt_enn b
    refine h_lint_mono.trans ?_
    have h_atom3 :
        AEStronglyMeasurable
          (fun b : M =>
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => |scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)
                (extChartAt I α b')|) b)
          μ :=
      aestronglyMeasurable_indicator_tsupp_abs_raw
        (I := I) (M := M) g r s α S Idx Jdx
    have h_rawInd_sq_eq :
        ∀ b, (rawInd b) ^ 2 =
          ((tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
            (fun b' : M => |scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx)
              (extChartAt I α b')|) b) ^ 2 := by
      intro b
      by_cases hb : b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
      · have h1 : rawInd b = rawZ b := by
          change (tsupport _).indicator rawZ b = rawZ b
          exact Set.indicator_of_mem hb _
        have h2 :
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => |scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)
                (extChartAt I α b')|) b = |rawZ b| :=
          Set.indicator_of_mem hb _
        rw [h1, h2, sq_abs]
      · have h1 : rawInd b = 0 := by
          change (tsupport _).indicator rawZ b = 0
          exact Set.indicator_of_notMem hb _
        have h2 :
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => |scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)
                (extChartAt I α b')|) b = 0 :=
          Set.indicator_of_notMem hb _
        rw [h1, h2]
    have h_f1_ae_str : AEStronglyMeasurable f1 μ := by
      have h_sq : AEStronglyMeasurable (fun b : M => (rawInd b) ^ 2) μ := by
        have : (fun b : M => (rawInd b) ^ 2) =
            (fun b : M =>
              ((tsupport (fun x : M =>
                  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
                (fun b' : M => |scalarOnE (I := I) α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx)
                  (extChartAt I α b')|) b) ^ 2) := by
          funext b; exact h_rawInd_sq_eq b
        rw [this]
        exact (continuous_pow 2).comp_aestronglyMeasurable h_atom3
      have h_A_sq : AEStronglyMeasurable (fun b : M => A * (rawInd b) ^ 2) μ :=
        h_sq.const_mul A
      exact (ENNReal.continuous_ofReal.comp_aestronglyMeasurable h_A_sq :
        AEStronglyMeasurable (fun b : M => ENNReal.ofReal (A * (rawInd b) ^ 2)) μ)
    have h_f1_aemeas : AEMeasurable f1 μ := h_f1_ae_str.aemeasurable
    have h_atom1 :
        AEStronglyMeasurable
          (fun b : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
              Real.sqrt
                (∑ k : Fin (Module.finrank ℝ E),
                  ‖chartTensorRSCovariantDerivative (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b‖ ^ 2))
          μ :=
      chartTensorRSCovariantDerivative_pouWeightedNorm_aestronglyMeasurable (I := I) (M := M) g r s α S
    have h_Tcov_nn_pt : ∀ b, 0 ≤ Tcov b := fun b => by
      rw [hTcov_def]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h_rho_Tcov_sq_eq : ∀ b,
        (ρ b) ^ 2 * Tcov b =
          (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b‖ ^ 2)) ^ 2 := by
      intro b
      have h_sum_eq :
          (∑ k : Fin (Module.finrank ℝ E),
              ‖chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α k) b‖ ^ 2) = Tcov b := by
        rw [hTcov_def]
      have h_Tcov_pt_nn : (0 : ℝ) ≤ Tcov b := h_Tcov_nn_pt b
      have h_eq_inside :
          Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b‖ ^ 2) =
            Real.sqrt (Tcov b) := by
        rw [h_sum_eq]
      have hρ_eq : (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) = ρ b := by
        rw [hρ_def]
      rw [hρ_eq, h_eq_inside, mul_pow,
        show Real.sqrt (Tcov b) ^ 2 = Tcov b from Real.sq_sqrt h_Tcov_pt_nn]
    have h_f2_ae_str : AEStronglyMeasurable f2 μ := by
      have h_sq : AEStronglyMeasurable (fun b : M => (ρ b) ^ 2 * Tcov b) μ := by
        have hfun_eq :
            (fun b : M => (ρ b) ^ 2 * Tcov b) =
              (fun b : M =>
                (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                  Real.sqrt
                    (∑ k : Fin (Module.finrank ℝ E),
                      ‖chartTensorRSCovariantDerivative (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α k) b‖ ^ 2)) ^ 2) := by
          funext b; exact h_rho_Tcov_sq_eq b
        rw [hfun_eq]
        exact (continuous_pow 2).comp_aestronglyMeasurable h_atom1
      have h_B_sq : AEStronglyMeasurable
          (fun b : M => B * ((ρ b) ^ 2 * Tcov b)) μ := h_sq.const_mul B
      have hrearr : (fun b : M => B * ((ρ b) ^ 2 * Tcov b)) =
          (fun b : M => B * (ρ b) ^ 2 * Tcov b) := by
        funext b; ring
      rw [hrearr] at h_B_sq
      exact ENNReal.continuous_ofReal.comp_aestronglyMeasurable h_B_sq
    have h_f2_aemeas : AEMeasurable f2 μ := h_f2_ae_str.aemeasurable
    have h_split12 :
        ∫⁻ b, f1 b + f2 b + f3 b ∂μ =
          ∫⁻ b, f1 b ∂μ + ∫⁻ b, f2 b + f3 b ∂μ := by
      have hg_eq :
          (fun b : M => f1 b + f2 b + f3 b) =
            (fun b : M => f1 b + (f2 b + f3 b)) := by
        funext b; rw [add_assoc]
      rw [show (∫⁻ b, f1 b + f2 b + f3 b ∂μ) =
          ∫⁻ b, f1 b + (f2 b + f3 b) ∂μ from by rw [hg_eq]]
      exact lintegral_add_left' h_f1_aemeas _
    have h_split23 :
        ∫⁻ b, f2 b + f3 b ∂μ = ∫⁻ b, f2 b ∂μ + ∫⁻ b, f3 b ∂μ :=
      lintegral_add_left' h_f2_aemeas _
    rw [h_split12, h_split23]
    have h_G4_S : eLpNorm rawInd 2 μ ≤ ENNReal.ofReal C₄ * (‖S‖₊ : ℝ≥0∞) := by
      have := h_G4 S Idx Jdx
      have h_fun_eq :
          (fun b : M =>
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M =>
                scalarOnE (I := I) α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx)
                  (extChartAt I α b')) b) = rawInd := by
        funext b; rfl
      rw [h_fun_eq] at this
      exact this
    have h_f1_int : ∫⁻ b, f1 b ∂μ ≤ ENNReal.ofReal (A * C₄ ^ 2 * ‖S‖ ^ 2) := by
      have h_f1_eq :
          ∀ b, f1 b = ENNReal.ofReal A * (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 := by
        intro b
        have h_enn_sq : (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 =
            ENNReal.ofReal ((rawInd b) ^ 2) := by
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
            sq_abs]
        change ENNReal.ofReal (A * (rawInd b) ^ 2) =
          ENNReal.ofReal A * (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2
        rw [h_enn_sq, ENNReal.ofReal_mul hA_nn]
      have h_int_eq :
          ∫⁻ b, f1 b ∂μ =
            ENNReal.ofReal A * ∫⁻ b, (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
        rw [show (∫⁻ b, f1 b ∂μ) =
            ∫⁻ b, ENNReal.ofReal A * (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ from by
          refine lintegral_congr ?_; intro b; exact h_f1_eq b]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      have h_G4_sq : (eLpNorm rawInd 2 μ) ^ 2 ≤
          ENNReal.ofReal (C₄ ^ 2 * ‖S‖ ^ 2) := by
        have h_pow_mono := pow_le_pow_left' h_G4_S 2
        have h_pow_rhs :
            (ENNReal.ofReal C₄ * (‖S‖₊ : ℝ≥0∞)) ^ 2 =
              ENNReal.ofReal (C₄ ^ 2 * ‖S‖ ^ 2) := by
          rw [mul_pow, ← ENNReal.ofReal_pow hC₄_nn,
            show ((‖S‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖S‖ ^ 2) from by
              rw [show ((‖S‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖S‖ from
                  coe_nnnorm_eq_ofReal_norm S,
                ← ENNReal.ofReal_pow (norm_nonneg _)],
            ← ENNReal.ofReal_mul (by positivity)]
        rw [h_pow_rhs] at h_pow_mono
        exact h_pow_mono
      have h_G4_sq_lint :
          ∫⁻ b, (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
            ENNReal.ofReal (C₄ ^ 2 * ‖S‖ ^ 2) := by
        have h_eLp_sq_eq : (eLpNorm rawInd 2 μ) ^ 2 =
            ∫⁻ b, (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
          have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
          have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
          have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by
            show ENNReal.toReal 2 = 2; rfl
          rw [h2_toReal]
          have h_inner_eq : ∫⁻ b, (‖rawInd b‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
              ∫⁻ b, (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
            refine lintegral_congr_ae ?_
            filter_upwards with b
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
              ENNReal.rpow_natCast]
          rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
          norm_num
        rw [← h_eLp_sq_eq]; exact h_G4_sq
      calc ∫⁻ b, f1 b ∂μ
          = ENNReal.ofReal A * ∫⁻ b, (‖rawInd b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := h_int_eq
        _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C₄ ^ 2 * ‖S‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h_G4_sq_lint (zero_le _)
        _ = ENNReal.ofReal (A * (C₄ ^ 2 * ‖S‖ ^ 2)) :=
            (ENNReal.ofReal_mul hA_nn).symm
        _ = ENNReal.ofReal (A * C₄ ^ 2 * ‖S‖ ^ 2) := by
            congr 1; ring
    have h_G2_S := h_G2 S Idx Jdx
    have h_f2_int : ∫⁻ b, f2 b ∂μ ≤ ENNReal.ofReal (B * C₂ ^ 2 * ‖S‖ ^ 2) := by
      set h2 : M → ℝ := fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α k) b‖ ^ 2)
        with hh2_def
      have h_f2_eq :
          ∀ b, f2 b = ENNReal.ofReal B * (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 := by
        intro b
        have h_rho_Tcov : (ρ b) ^ 2 * Tcov b = (h2 b) ^ 2 := h_rho_Tcov_sq_eq b
        have h_enn_sq : (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 =
            ENNReal.ofReal ((h2 b) ^ 2) := by
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
            sq_abs]
        change ENNReal.ofReal (B * (ρ b) ^ 2 * Tcov b) =
          ENNReal.ofReal B * (‖h2 b‖ₑ : ℝ≥0∞) ^ 2
        rw [h_enn_sq, show B * (ρ b) ^ 2 * Tcov b = B * ((ρ b) ^ 2 * Tcov b)
          from by ring, h_rho_Tcov, ENNReal.ofReal_mul hB_nn]
      have h_int_eq :
          ∫⁻ b, f2 b ∂μ =
            ENNReal.ofReal B * ∫⁻ b, (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
        rw [show (∫⁻ b, f2 b ∂μ) =
            ∫⁻ b, ENNReal.ofReal B * (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ from by
          refine lintegral_congr ?_; intro b; exact h_f2_eq b]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      have h_G2_sq : (eLpNorm h2 2 μ) ^ 2 ≤
          ENNReal.ofReal (C₂ ^ 2 * ‖S‖ ^ 2) := by
        have h_pow_mono := pow_le_pow_left' h_G2_S 2
        have h_pow_rhs :
            (ENNReal.ofReal C₂ * (‖S‖₊ : ℝ≥0∞)) ^ 2 =
              ENNReal.ofReal (C₂ ^ 2 * ‖S‖ ^ 2) := by
          rw [mul_pow, ← ENNReal.ofReal_pow hC₂_nn,
            show ((‖S‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖S‖ ^ 2) from by
              rw [show ((‖S‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖S‖ from
                  coe_nnnorm_eq_ofReal_norm S,
                ← ENNReal.ofReal_pow (norm_nonneg _)],
            ← ENNReal.ofReal_mul (by positivity)]
        rw [h_pow_rhs] at h_pow_mono
        exact h_pow_mono
      have h_G2_sq_lint :
          ∫⁻ b, (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
            ENNReal.ofReal (C₂ ^ 2 * ‖S‖ ^ 2) := by
        have h_eLp_sq_eq : (eLpNorm h2 2 μ) ^ 2 =
            ∫⁻ b, (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
          have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
          have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
          have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by
            show ENNReal.toReal 2 = 2; rfl
          rw [h2_toReal]
          have h_inner_eq : ∫⁻ b, (‖h2 b‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
              ∫⁻ b, (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
            refine lintegral_congr_ae ?_
            filter_upwards with b
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
              ENNReal.rpow_natCast]
          rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
          norm_num
        rw [← h_eLp_sq_eq]; exact h_G2_sq
      calc ∫⁻ b, f2 b ∂μ
          = ENNReal.ofReal B * ∫⁻ b, (‖h2 b‖ₑ : ℝ≥0∞) ^ 2 ∂μ := h_int_eq
        _ ≤ ENNReal.ofReal B * ENNReal.ofReal (C₂ ^ 2 * ‖S‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h_G2_sq_lint (zero_le _)
        _ = ENNReal.ofReal (B * (C₂ ^ 2 * ‖S‖ ^ 2)) :=
            (ENNReal.ofReal_mul hB_nn).symm
        _ = ENNReal.ofReal (B * C₂ ^ 2 * ‖S‖ ^ 2) := by
            congr 1; ring
    have h_f3_int : ∫⁻ b, f3 b ∂μ ≤ ENNReal.ofReal (C₃ * ‖S‖ ^ 2) := by
      set TIP : M → ℝ := fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) with hTIP_def
      have hTIP_nn : ∀ b, 0 ≤ TIP b := fun b =>
        tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
      set C₃' : ℝ := B * C_bridge * (n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2
        with hC₃'_def
      have hC₃'_nn : 0 ≤ C₃' := by rw [hC₃'_def]; positivity
      have hC₃'_eq : C₃' = C₃ := by rw [hC₃'_def, hC₃_def]
      have h_secSq_eq : ∀ b : M, ‖S.toCcTensor.toSection b‖ ^ 2 = TIP b := by
        intro b
        change ‖S.toCcTensor.toSection b‖ ^ 2 =
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)
        have h_inner : (⟪S.toCcTensor.toSection b, S.toCcTensor.toSection b⟫_ℝ : ℝ) =
            tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) := by
          change tensorRSRiemannianInnerCLM (I := I) (M := M) g r s b
              (S.toCcTensor.toSection b) (S.toCcTensor.toSection b) = _
          rw [tensorRSRiemannianInnerCLM_apply]
          rfl
        rw [← h_inner]
        exact (real_inner_self_eq_norm_sq _).symm
      have h_pt_f3 : ∀ b,
          B * C_bridge * (ρ b) ^ 2 * TchrSumK b ≤ C₃' * TIP b := by
        intro b
        by_cases hb : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
        · have h_rho_le_one : ρ b ≤ 1 := by
            rw [hρ_def]; exact (chartAtlasPOU I M).le_one α b
          have h_rho_nn_b : 0 ≤ ρ b := hρ_nn b
          have h_rho_sq_le_one : (ρ b) ^ 2 ≤ 1 := by
            rw [sq]
            calc ρ b * ρ b ≤ 1 * 1 :=
                  mul_le_mul h_rho_le_one h_rho_le_one h_rho_nn_b zero_le_one
              _ = 1 := by ring
          have h_in_le : ∀ k : Fin (Module.finrank ℝ E), ∀ i : Fin r,
              ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α k) b i‖ ≤
                M_F * ‖S.toCcTensor.toSection b‖ := by
            intro k i
            have h_orig := hM_F_in_le (fun b' => S.toCcTensor.toSection b')
              (b := b) hb k i
            exact h_orig.trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
          have h_out_le : ∀ k : Fin (Module.finrank ℝ E), ∀ l : Fin s,
              ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α k) b l‖ ≤
                M_F * ‖S.toCcTensor.toSection b‖ := by
            intro k l
            have h_orig := hM_F_out_le (fun b' => S.toCcTensor.toSection b')
              (b := b) hb k l
            exact h_orig.trans
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
          have h_norm_sec_nn : 0 ≤ ‖S.toCcTensor.toSection b‖ := norm_nonneg _
          have h_perk : ∀ k : Fin (Module.finrank ℝ E),
              TchrPerK k b ≤
                ((r : ℝ) + (s : ℝ)) * M_F ^ 2 * ‖S.toCcTensor.toSection b‖ ^ 2 := by
            intro k
            rw [hTchrPerK_def]
            have h_sum_in_le :
                (∑ i : Fin r,
                  ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b i‖ ^ 2) ≤
                  (r : ℝ) * (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 := by
              calc (∑ i : Fin r,
                  ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b i‖ ^ 2)
                  ≤ ∑ _i : Fin r, (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 :=
                    Finset.sum_le_sum (fun i _ =>
                      pow_le_pow_left₀ (norm_nonneg _) (h_in_le k i) 2)
                _ = (r : ℝ) * (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 := by
                    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
            have h_sum_out_le :
                (∑ l : Fin s,
                  ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b l‖ ^ 2) ≤
                  (s : ℝ) * (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 := by
              calc (∑ l : Fin s,
                  ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b l‖ ^ 2)
                  ≤ ∑ _l : Fin s, (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 :=
                    Finset.sum_le_sum (fun l _ =>
                      pow_le_pow_left₀ (norm_nonneg _) (h_out_le k l) 2)
                _ = (s : ℝ) * (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 := by
                    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
            have h_combined :
                (∑ i : Fin r,
                  ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b i‖ ^ 2) +
                  (∑ l : Fin s,
                  ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b l‖ ^ 2) ≤
                ((r : ℝ) + (s : ℝ)) *
                  (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 := by
              have := add_le_add h_sum_in_le h_sum_out_le; linarith
            have h_mul_eq :
                ((r : ℝ) + (s : ℝ)) *
                  (M_F * ‖S.toCcTensor.toSection b‖) ^ 2 =
                ((r : ℝ) + (s : ℝ)) * M_F ^ 2 *
                  ‖S.toCcTensor.toSection b‖ ^ 2 := by
              rw [mul_pow]; ring
            rw [← h_mul_eq]; exact h_combined
          have h_sumK_le :
              TchrSumK b ≤
                (n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2 *
                  ‖S.toCcTensor.toSection b‖ ^ 2 := by
            rw [hTchrSumK_def]
            calc (∑ k : Fin (Module.finrank ℝ E), TchrPerK k b)
                ≤ ∑ _k : Fin (Module.finrank ℝ E),
                    (((r : ℝ) + (s : ℝ)) * M_F ^ 2 *
                      ‖S.toCcTensor.toSection b‖ ^ 2) :=
                  Finset.sum_le_sum (fun k _ => h_perk k)
              _ = (n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2 *
                    ‖S.toCcTensor.toSection b‖ ^ 2 := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hn_def]
                  ring
          have h_sumK_le' :
              TchrSumK b ≤
                (n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2 * TIP b := by
            rw [← h_secSq_eq b]; exact h_sumK_le
          have h_pre_nn : 0 ≤ (n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2 := by
            positivity
          have h_BCB_nn : 0 ≤ B * C_bridge := mul_nonneg hB_nn hC_bridge_nn
          have h_BCB_rho_sq_le : B * C_bridge * (ρ b) ^ 2 ≤ B * C_bridge := by
            have : B * C_bridge * (ρ b) ^ 2 ≤ B * C_bridge * 1 :=
              mul_le_mul_of_nonneg_left h_rho_sq_le_one h_BCB_nn
            linarith
          have h_TchrSumK_nn_b : 0 ≤ TchrSumK b := by
            rw [hTchrSumK_def]
            refine Finset.sum_nonneg (fun k _ => ?_)
            rw [hTchrPerK_def]
            exact add_nonneg
              (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
              (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
          calc B * C_bridge * (ρ b) ^ 2 * TchrSumK b
              ≤ B * C_bridge * TchrSumK b :=
                mul_le_mul_of_nonneg_right h_BCB_rho_sq_le h_TchrSumK_nn_b
            _ ≤ B * C_bridge * ((n : ℝ) * ((r : ℝ) + (s : ℝ)) * M_F ^ 2 * TIP b) :=
                mul_le_mul_of_nonneg_left h_sumK_le' h_BCB_nn
            _ = C₃' * TIP b := by rw [hC₃'_def]; ring
        · have h_ρ_zero : ρ b = 0 := by
            by_contra hne
            exact hb (subset_tsupport _ hne)
          have hRHS_nn : 0 ≤ C₃' * TIP b := mul_nonneg hC₃'_nn (hTIP_nn b)
          rw [h_ρ_zero]; simpa using hRHS_nn
      have h_pt_enn3 : ∀ b, f3 b ≤ ENNReal.ofReal (C₃' * TIP b) := by
        intro b
        rw [hf3_def]
        exact ENNReal.ofReal_le_ofReal (h_pt_f3 b)
      have h_mono : ∫⁻ b, f3 b ∂μ ≤
          ∫⁻ b, ENNReal.ofReal (C₃' * TIP b) ∂μ :=
        lintegral_mono h_pt_enn3
      have h_TIP_int : Integrable TIP μ := by
        rw [hμ_def, hTIP_def]
        exact SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
          S.toCcTensor S.toCcTensor
      have h_CTIP_int : Integrable (fun b => C₃' * TIP b) μ :=
        h_TIP_int.const_mul C₃'
      have h_CTIP_ae_nn : 0 ≤ᵐ[μ] (fun b => C₃' * TIP b) :=
        Filter.Eventually.of_forall (fun b => mul_nonneg hC₃'_nn (hTIP_nn b))
      have h_lint_to_int :
          ∫⁻ b, ENNReal.ofReal (C₃' * TIP b) ∂μ =
            ENNReal.ofReal (∫ b, C₃' * TIP b ∂μ) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_CTIP_int h_CTIP_ae_nn).symm
      have h_int_TIP_le : ∫ b, TIP b ∂μ ≤ ‖S‖ ^ 2 := by
        have h_l2_eq : ∫ b, TIP b ∂μ = ‖S.toCcTensor‖ ^ 2 := by
          rw [hTIP_def, hμ_def]
          have h_eq : ∫ b,
              tensorInnerPointwise (I := I) (M := M) g r s b
                (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
            tensorL2Inner (I := I) (M := M) g r s
              S.toCcTensor.toFun S.toCcTensor.toFun := rfl
          rw [h_eq, ← SmoothCcTensor.norm_sq_eq_inner_self
            (I := I) (M := M) S.toCcTensor]
        rw [h_l2_eq]
        exact SmoothCcTensorH1.l2NormSq_le_h1NormSq S
      have h_int_CTIP_le : ∫ b, C₃' * TIP b ∂μ ≤ C₃' * ‖S‖ ^ 2 := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left h_int_TIP_le hC₃'_nn
      calc ∫⁻ b, f3 b ∂μ
          ≤ ∫⁻ b, ENNReal.ofReal (C₃' * TIP b) ∂μ := h_mono
        _ = ENNReal.ofReal (∫ b, C₃' * TIP b ∂μ) := h_lint_to_int
        _ ≤ ENNReal.ofReal (C₃' * ‖S‖ ^ 2) :=
            ENNReal.ofReal_le_ofReal h_int_CTIP_le
        _ = ENNReal.ofReal (C₃ * ‖S‖ ^ 2) := by rw [hC₃'_eq]
    have h_sum_le :
        ∫⁻ b, f1 b ∂μ + (∫⁻ b, f2 b ∂μ + ∫⁻ b, f3 b ∂μ) ≤
          ENNReal.ofReal (A * C₄ ^ 2 * ‖S‖ ^ 2) +
            (ENNReal.ofReal (B * C₂ ^ 2 * ‖S‖ ^ 2) +
              ENNReal.ofReal (C₃ * ‖S‖ ^ 2)) :=
      add_le_add h_f1_int (add_le_add h_f2_int h_f3_int)
    refine h_sum_le.trans ?_
    have hA_sq_nn : 0 ≤ A * C₄ ^ 2 * ‖S‖ ^ 2 :=
      mul_nonneg (mul_nonneg hA_nn (sq_nonneg _)) (sq_nonneg _)
    have hB_sq_nn : 0 ≤ B * C₂ ^ 2 * ‖S‖ ^ 2 :=
      mul_nonneg (mul_nonneg hB_nn (sq_nonneg _)) (sq_nonneg _)
    have hC3_sq_nn : 0 ≤ C₃ * ‖S‖ ^ 2 := mul_nonneg hC₃_nn (sq_nonneg _)
    have h_sum_pos : 0 ≤ B * C₂ ^ 2 * ‖S‖ ^ 2 + C₃ * ‖S‖ ^ 2 :=
      add_nonneg hB_sq_nn hC3_sq_nn
    rw [← ENNReal.ofReal_add hB_sq_nn hC3_sq_nn,
      ← ENNReal.ofReal_add hA_sq_nn h_sum_pos]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hC_sq_def]; ring_nf; linarith
  have h_sq_nn : 0 ≤ C_sq * ‖S‖ ^ 2 := mul_nonneg hC_sq_nn (sq_nonneg _)
  have h_eLpNorm_le : eLpNorm TinnerSqrt 2 μ ≤
      ENNReal.ofReal (Real.sqrt (C_sq * ‖S‖ ^ 2)) := by
    have h_pow : eLpNorm TinnerSqrt 2 μ =
        ((eLpNorm TinnerSqrt 2 μ) ^ 2) ^ ((1 : ℝ) / 2) := by
      rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
      norm_num
    rw [h_pow]
    refine (ENNReal.rpow_le_rpow h_sq_bound (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans ?_
    have h_X_decomp : ENNReal.ofReal (C_sq * ‖S‖ ^ 2) =
        ENNReal.ofReal (Real.sqrt (C_sq * ‖S‖ ^ 2)) ^ 2 := by
      have h_sq_eq : Real.sqrt (C_sq * ‖S‖ ^ 2) *
          Real.sqrt (C_sq * ‖S‖ ^ 2) = C_sq * ‖S‖ ^ 2 := Real.mul_self_sqrt h_sq_nn
      rw [show ENNReal.ofReal (Real.sqrt (C_sq * ‖S‖ ^ 2)) ^ 2 =
          ENNReal.ofReal (Real.sqrt (C_sq * ‖S‖ ^ 2)) *
            ENNReal.ofReal (Real.sqrt (C_sq * ‖S‖ ^ 2)) from sq _,
        ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), h_sq_eq]
    rw [h_X_decomp]
    rw [← ENNReal.rpow_natCast (ENNReal.ofReal (Real.sqrt (C_sq * ‖S‖ ^ 2))) 2,
      ← ENNReal.rpow_mul]
    rw [show ((2 : ℕ) : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  refine h_eLpNorm_le.trans ?_
  have hS_nn : 0 ≤ ‖S‖ := norm_nonneg _
  have h_sqrt_fact : Real.sqrt (C_sq * ‖S‖ ^ 2) = C * ‖S‖ := by
    rw [hC_def, Real.sqrt_mul hC_sq_nn,
      show ‖S‖ ^ 2 = ‖S‖ * ‖S‖ from by ring, Real.sqrt_mul_self hS_nn]
  rw [h_sqrt_fact, ENNReal.ofReal_mul hC_nn,
    show ENNReal.ofReal ‖S‖ = (‖S‖₊ : ℝ≥0∞) from
      (coe_nnnorm_eq_ofReal_norm S).symm]

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry

end
