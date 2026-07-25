import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHSEigenvalueBounds.EigenvectorChartRHSDiffWkpNormSharpBounded


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma sharpDiffExplicit_wkpNorm_sub_le
    {K : ℕ} {Ω : Set EuclN}
    (hΩ : IsOpen Ω) {u v : EuclN → ℝ}
    (hu : MemWkp (d := Module.finrank ℝ E) K 2 u Ω)
    (hv : MemWkp (d := Module.finrank ℝ E) K 2 v Ω) :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (fun y => u y - v y) Ω ≤
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 u Ω
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 v Ω := by
  classical
  have h_fun : (fun y => u y - v y) = (fun y => u y + (fun y => - v y) y) := by
    funext y; ring
  rw [h_fun]
  have hv_neg : MemWkp (d := Module.finrank ℝ E) K 2 (fun y => - v y) Ω :=
    MemWkp.neg (d := Module.finrank ℝ E) (by norm_num) hΩ hv
  refine le_trans (wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ hu hv_neg) ?_
  have h_neg_eq : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (fun y => - v y) Ω =
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 v Ω := by
    have h_smul : (fun y => - v y) = (fun y => (-1 : ℝ) * v y) := by
      funext y; ring
    rw [h_smul, wkpNorm_const_smul (d := Module.finrank ℝ E) (by norm_num) hΩ hv (-1)]
    simp
  rw [h_neg_eq]

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in

omit [NeZero (Module.finrank ℝ E)] in
private lemma sharpDiffExplicit_layerA_coeff_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_diffOn : ContDiffOn ℝ (⊤ : ℕ∞)
      (weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)))
      (chartTargetEuclid (I := I) (M := M) α) :=
    weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m))
  have h_fderiv : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
          (l (Fin.last m))) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen h_open).1 h_diffOn).2
  have h_eval : ContDiff ℝ (⊤ : ℕ∞)
      (fun (L : EuclN →L[ℝ] ℝ) => L (EuclideanSpace.single b 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single b (1 : ℝ))).contDiff
  exact h_eval.contDiffOn.comp h_fderiv (mapsTo_univ _ _)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1000000 in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma rhsZeroAggregate_le_at_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K N target : ℕ)
    (hKN : K + 1 ≤ N)
    (H : eigenvectorChartRHSDiffSharpWkpBoundsUpToOrder (I := I) (M := M) g r s α P₀ N)
    (hEig_le : H.eEig K ≤ target)
    (hResH_le_K : H.eResH K ≤ target)
    (hResL_le : H.eResL K ≤ target)
    (hPar_le : H.ePar K ≤ target)
    (hCom_le : H.eCom K ≤ target)
    (hCcR_le : H.eCcR K ≤ target)
    (hCcut_le : H.eCcut K ≤ target) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        rhsZeroAggregate (I := I) (M := M) g r s i α P₀ K
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ target) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  have hK_le_N : K ≤ N := by omega
  set Cqtot : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * H.CresH K
    with hCqtot_def
  set Cmid_α : ℝ := (transportChartCenters (I := I) (M := M) α).sum fun β =>
        Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot
    with hCmid_α_def
  set Clow_α : ℝ :=
    ((transportChartCenters (I := I) (M := M) α).card : ℝ) *
      ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * H.CresL K) with hClow_α_def
  set Cpar' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.Cpar K) with hCpar'_def
  set Ccom' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * H.Ccom K
    with hCcom'_def
  set CcR' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * H.CcR K
    with hCcR'_def
  set Ccut' : ℝ := (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) *
        ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.Ccut K) with hCcut'_def
  set Cagg : ℝ := H.Ceig K + Cmid_α + Clow_α + Cpar' + Ccom' + CcR' + Ccut'
    with hCagg_def
  have hCqtot_nn : 0 ≤ Cqtot := by
    have h := H.hCresH_nn K; positivity
  have hCmid_α_nn : 0 ≤ Cmid_α := by
    refine Finset.sum_nonneg (fun β _ => ?_)
    have h : (0 : ℝ) ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    exact add_nonneg hCqtot_nn (mul_nonneg h hCqtot_nn)
  have hClow_α_nn : 0 ≤ Clow_α := by
    have h := H.hCresL_nn K; positivity
  have hCpar'_nn : 0 ≤ Cpar' := by
    have h := H.hCpar_nn K; positivity
  have hCcom'_nn : 0 ≤ Ccom' := by
    have h := H.hCcom_nn K; positivity
  have hCcR'_nn : 0 ≤ CcR' := by
    have h := H.hCcR_nn K; positivity
  have hCcut'_nn : 0 ≤ Ccut' := by
    have h := H.hCcut_nn K; positivity
  have hCagg_nn : 0 ≤ Cagg := by
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (add_nonneg ?_ hCmid_α_nn) hClow_α_nn) hCpar'_nn) hCcom'_nn) hCcR'_nn) hCcut'_nn
    exact H.hCeig_nn K
  refine ⟨Cagg, hCagg_nn, fun i => ?_⟩
  have hμ_inv_ge_one : (1 : ℝ) ≤ (i.fst.val)⁻¹ :=
    sharpDiff_eigen_inv_one_le (I := I) (M := M) g r s i
  have hpow_dom : ∀ a, a ≤ target → (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ target :=
    fun _a ha => pow_le_pow_right₀ hμ_inv_ge_one ha
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i‖
    with hRhs_def
  set Rhs_eff : ℝ≥0∞ := ENNReal.ofReal ((i.fst.val)⁻¹ ^ target) * Rhs
    with hRhs_eff_def
  have h_bridge : ∀ (w : ℝ≥0∞) (Cval : ℝ) (a : ℕ),
      0 ≤ Cval → a ≤ target →
      w ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ a) * Rhs →
      w ≤ ENNReal.ofReal Cval * Rhs_eff := by
    intro w Cval a hCval_nn ha hw
    have hpow_le : (i.fst.val)⁻¹ ^ a ≤ (i.fst.val)⁻¹ ^ target := hpow_dom a ha
    have hCmul_le : Cval * (i.fst.val)⁻¹ ^ a ≤ Cval * (i.fst.val)⁻¹ ^ target :=
      mul_le_mul_of_nonneg_left hpow_le hCval_nn
    have h_eNN_le : ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ a)
          ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ target) :=
      ENNReal.ofReal_le_ofReal hCmul_le
    have h_step : w ≤ ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ target) * Rhs := by
      refine hw.trans ?_
      exact mul_le_mul_of_nonneg_right h_eNN_le (by exact zero_le _)
    have h_rw : ENNReal.ofReal (Cval * (i.fst.val)⁻¹ ^ target) * Rhs
          = ENNReal.ofReal Cval * Rhs_eff := by
      rw [hRhs_eff_def, ENNReal.ofReal_mul hCval_nn, mul_assoc]
    exact h_step.trans_eq h_rw
  have hS1 :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (H.Ceig K) * Rhs_eff :=
    h_bridge _ (H.Ceig K) (H.eEig K) (H.hCeig_nn K) hEig_le
      (H.hCeig_bd i K hK_le_N)
  have hS2_inner : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
      ((∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
        ≤ ENNReal.ofReal
            (Cqtot + ((transportChartCenters (I := I) (M := M) β).card : ℝ) *
              Cqtot) * Rhs_eff := by
    intro β _hβ
    have h_inner_β :
        (∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal Cqtot * Rhs_eff := by
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal (H.CresH K) * Rhs_eff := fun Q _hQ =>
        h_bridge _ (H.CresH K) (H.eResH K) (H.hCresH_nn K) hResH_le_K
          (H.hCresH_bd i β Q K hKN)
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => H.CresH K) Rhs_eff (fun _ _ => H.hCresH_nn K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum.trans_eq (by rw [hCqtot_def])
    have h_inner_β' :
        (∑ β' ∈ transportChartCenters (I := I) (M := M) β,
          ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
        ≤ ENNReal.ofReal
            (((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot) *
            Rhs_eff := by
      have h_perβ' : ∀ β' ∈ transportChartCenters (I := I) (M := M) β,
          (∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
            ≤ ENNReal.ofReal Cqtot * Rhs_eff := by
        intro β' _hβ'
        have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s i))
                    β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β')
              ≤ ENNReal.ofReal (H.CresH K) * Rhs_eff := fun Q _hQ =>
          h_bridge _ (H.CresH K) (H.eResH K) (H.hCresH_nn K) hResH_le_K
            (H.hCresH_bd i β' Q K hKN)
        have h_sum := finsetSum_eNNReal_ofReal_mul_le
          (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun Q => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
          (fun _Q => H.CresH K) Rhs_eff (fun _ _ => H.hCresH_nn K) h_each
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
        exact h_sum.trans_eq (by rw [hCqtot_def])
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (transportChartCenters (I := I) (M := M) β)
        (fun β' => ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β' Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β'))
        (fun _β' => Cqtot) Rhs_eff (fun _ _ => hCqtot_nn) h_perβ'
      rw [Finset.sum_const, nsmul_eq_mul] at h_sum
      exact h_sum
    have h_total :=
      add_le_add h_inner_β h_inner_β'
    refine h_total.trans (le_of_eq ?_)
    have hN : 0 ≤ ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    rw [ENNReal.ofReal_add hCqtot_nn (mul_nonneg hN hCqtot_nn), add_mul]
  have hS2 :
      (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ((∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M) g r s i))
                    β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β))
          + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
              ∑ Q : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s i))
                      β' Q :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β')))
      ≤ ENNReal.ofReal Cmid_α * Rhs_eff := by
    have h_perβ_nn :
        ∀ β ∈ transportChartCenters (I := I) (M := M) α,
          0 ≤ Cqtot +
              ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot := by
      intro β _hβ
      have hN : (0 : ℝ) ≤
          ((transportChartCenters (I := I) (M := M) β).card : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact add_nonneg hCqtot_nn (mul_nonneg hN hCqtot_nn)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (transportChartCenters (I := I) (M := M) α)
      (fun β => (∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
            ∑ Q : TensorCompIdx (E := E) r s,
              iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                      (eigenvectorResolvent (I := I) (M := M)
                        g r s i))
                    β' Q :
                    Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                    EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β'))
      (fun β => Cqtot +
        ((transportChartCenters (I := I) (M := M) β).card : ℝ) * Cqtot)
      Rhs_eff h_perβ_nn hS2_inner
    exact h_sum.trans_eq (by rw [hCmid_α_def])
  have hS3 :
      (∑ β ∈ transportChartCenters (I := I) (M := M) α,
        ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      ≤ ENNReal.ofReal Clow_α * Rhs_eff := by
    have h_perβ : ∀ β ∈ transportChartCenters (I := I) (M := M) α,
        (∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
          ≤ ENNReal.ofReal
              ((Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * H.CresL K) *
            Rhs_eff := by
      intro β _hβ
      have h_each : ∀ Q ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β)
            ≤ ENNReal.ofReal (H.CresL K) * Rhs_eff := fun Q _hQ =>
        h_bridge _ (H.CresL K) (H.eResL K) (H.hCresL_nn K) hResL_le
          (H.hCresL_bd i β Q K hK_le_N)
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
        (fun _Q => H.CresL K) Rhs_eff (fun _ _ => H.hCresL_nn K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hQ_nn : (0 : ℝ) ≤
        (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * H.CresL K := by
      have hQ : (0 : ℝ) ≤ (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hQ (H.hCresL_nn K)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (transportChartCenters (I := I) (M := M) α)
      (fun β => ∑ Q : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β))
      (fun _β => (Fintype.card (TensorCompIdx (E := E) r s) : ℝ) * H.CresL K)
      Rhs_eff (fun _ _ => hQ_nn) h_perβ
    rw [Finset.sum_const, nsmul_eq_mul] at h_sum
    exact h_sum.trans_eq (by rw [hClow_α_def])
  have hS4 :
      (∑ P : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Cpar' * Rhs_eff := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ k : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.Cpar K) *
            Rhs_eff := by
      intro P _hP
      have h_each : ∀ k ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.Cpar K) * Rhs_eff := fun k _hk =>
        h_bridge _ (H.Cpar K) (H.ePar K) (H.hCpar_nn K) hPar_le (H.hCpar_bd i P k K hKN)
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _k => H.Cpar K) Rhs_eff (fun _ _ => H.hCpar_nn K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.Cpar K := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk (H.hCpar_nn K)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ k : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((partialLpLimit (I := I) (M := M)
                g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.Cpar K)
      Rhs_eff (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCpar'_def])
  have hS5 :
      (∑ p : TensorCompIdx (E := E) r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Ccom' * Rhs_eff := by
    have h_each : ∀ p ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (H.Ccom K) * Rhs_eff := fun p _hp =>
      h_bridge _ (H.Ccom K) (H.eCom K) (H.hCcom_nn K) hCom_le (H.hCcom_bd i p K hK_le_N)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun p => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((componentLpLimit (I := I) (M := M)
              g r s i α p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _p => H.Ccom K) Rhs_eff (fun _ _ => H.hCcom_nn K) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcom'_def])
  have hS6 :
      (∑ P : TensorCompIdx (E := E) r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal CcR' * Rhs_eff := by
    have h_each : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (H.CcR K) * Rhs_eff := fun P _hP =>
      h_bridge _ (H.CcR K) (H.eCcR K) (H.hCcR_nn K) hCcR_le (H.hCcR_bd i P K hK_le_N)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
            EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => H.CcR K) Rhs_eff (fun _ _ => H.hCcR_nn K) h_each
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcR'_def])
  have hS7 :
      (∑ P : TensorCompIdx (E := E) r s,
        ∑ l : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      ≤ ENNReal.ofReal Ccut' * Rhs_eff := by
    have h_perP : ∀ P ∈ (Finset.univ : Finset (TensorCompIdx (E := E) r s)),
        (∑ l : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
          ≤ ENNReal.ofReal
              ((Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.Ccut K) *
            Rhs_eff := by
      intro P _hP
      have h_each : ∀ l ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.Ccut K) * Rhs_eff := fun l _hl =>
        h_bridge _ (H.Ccut K) (H.eCcut K) (H.hCcut_nn K) hCcut_le (H.hCcut_bd i P l K hKN)
      have h_sum := finsetSum_eNNReal_ofReal_mul_le
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        (fun _l => H.Ccut K) Rhs_eff (fun _ _ => H.hCcut_nn K) h_each
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
      exact h_sum
    have hk_nn : (0 : ℝ) ≤
        (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.Ccut K := by
      have hk : (0 : ℝ) ≤ (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) := by
        exact_mod_cast Nat.zero_le _
      exact mul_nonneg hk (H.hCcut_nn K)
    have h_sum := finsetSum_eNNReal_ofReal_mul_le
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P => ∑ l : Fin (Module.finrank ℝ E),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
      (fun _P => (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) * H.Ccut K)
      Rhs_eff (fun _ _ => hk_nn) h_perP
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at h_sum
    exact h_sum.trans_eq (by rw [hCcut'_def])
  rw [rhsZeroAggregate]
  have hp1 : 0 ≤ H.Ceig K + Cmid_α := add_nonneg (H.hCeig_nn K) hCmid_α_nn
  have hp2 : 0 ≤ H.Ceig K + Cmid_α + Clow_α := add_nonneg hp1 hClow_α_nn
  have hp3 : 0 ≤ H.Ceig K + Cmid_α + Clow_α + Cpar' := add_nonneg hp2 hCpar'_nn
  have hp4 : 0 ≤ H.Ceig K + Cmid_α + Clow_α + Cpar' + Ccom' :=
    add_nonneg hp3 hCcom'_nn
  have hp5 : 0 ≤ H.Ceig K + Cmid_α + Clow_α + Cpar' + Ccom' + CcR' :=
    add_nonneg hp4 hCcR'_nn
  have h_expand :
      ENNReal.ofReal Cagg
        = ENNReal.ofReal (H.Ceig K) + ENNReal.ofReal Cmid_α
          + ENNReal.ofReal Clow_α + ENNReal.ofReal Cpar' + ENNReal.ofReal Ccom'
          + ENNReal.ofReal CcR' + ENNReal.ofReal Ccut' := by
    rw [hCagg_def, ENNReal.ofReal_add hp5 hCcut'_nn,
      ENNReal.ofReal_add hp4 hCcR'_nn,
      ENNReal.ofReal_add hp3 hCcom'_nn,
      ENNReal.ofReal_add hp2 hCpar'_nn,
      ENNReal.ofReal_add hp1 hClow_α_nn,
      ENNReal.ofReal_add (H.hCeig_nn K) hCmid_α_nn]
  have h_sum_bound :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ((∑ Q : TensorCompIdx (E := E) r s,
                iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                  (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                      (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                        (eigenvectorResolvent (I := I) (M := M)
                          g r s i))
                      β Q :
                      Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                      EuclN → ℝ) y)
                  (chartTargetEuclid (I := I) (M := M) β))
            + ∑ β' ∈ transportChartCenters (I := I) (M := M) β,
                ∑ Q : TensorCompIdx (E := E) r s,
                  iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (K + 1) 2
                    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                          (eigenvectorResolvent (I := I) (M := M)
                            g r s i))
                        β' Q :
                        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β')) :
                        EuclN → ℝ) y)
                    (chartTargetEuclid (I := I) (M := M) β')))
        + (∑ β ∈ transportChartCenters (I := I) (M := M) α,
          ∑ Q : TensorCompIdx (E := E) r s,
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                    (eigenvectorResolvent (I := I) (M := M) g r s i))
                  β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        + (∑ P : TensorCompIdx (E := E) r s,
          ∑ k : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((partialLpLimit (I := I) (M := M)
                  g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
        + (∑ p : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((componentLpLimit (I := I) (M := M)
                g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        + (∑ P : TensorCompIdx (E := E) r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α))
        + (∑ P : TensorCompIdx (E := E) r s,
          ∑ l : Fin (Module.finrank ℝ E),
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                  g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
                EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α))
        ≤ ENNReal.ofReal Cagg * Rhs_eff := by
    rw [h_expand, add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]
    refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
      (add_le_add ?_ hS2) hS3) hS4) hS5) hS6) hS7
    exact hS1
  refine h_sum_bound.trans (le_of_eq ?_)
  rw [hRhs_eff_def, ← mul_assoc, ← ENNReal.ofReal_mul hCagg_nn]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma sharpDiffBdd_level_zero_wkpNorm_at_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K N target : ℕ)
    (hKN : K + 1 ≤ N)
    (H : eigenvectorChartRHSDiffSharpWkpBoundsUpToOrder (I := I) (M := M) g r s α P₀ N)
    (hEig_le : H.eEig K ≤ target)
    (hResH_le_K : H.eResH K ≤ target)
    (hResL_le : H.eResL K ≤ target)
    (hPar_le : H.ePar K ≤ target)
    (hCom_le : H.eCom K ≤ target)
    (hCcR_le : H.eCcR K ≤ target)
    (hCcut_le : H.eCcut K ≤ target) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (target + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨Cagg, hCagg_nn, hCagg_bd⟩ :=
    rhsZeroAggregate_le_at_target (I := I) (M := M) g r s α P₀ K N
      target hKN H hEig_le hResH_le_K hResL_le hPar_le hCom_le hCcR_le hCcut_le
  have h_pou : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
      (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) := fun i β Q =>
    H.h_pou_resolv i (K + 1) β Q hKN
  obtain ⟨Cmu, hCmu_nn, hCmu_bd⟩ :=
    eigenvectorChartRHS_wkpNorm_le_uniform (I := I) (M := M)
      g r s α P₀ K h_pou
  refine ⟨Cmu * Cagg, mul_nonneg hCmu_nn hCagg_nn, fun i => ?_⟩
  have hμ_inv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ :=
    sharpDiff_eigen_inv_nn (I := I) (M := M) g r s i
  have hμ_inv_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ target :=
    pow_nonneg hμ_inv_nn _
  have hCmu_aux := hCmu_bd i
  have hCagg_aux := hCagg_bd i
  change iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal ((i.fst.val)⁻¹ * Cmu) *
        rhsZeroAggregate (I := I) (M := M) g r s i α P₀ K at hCmu_aux
  refine le_trans hCmu_aux ?_
  refine le_trans (mul_le_mul' (le_refl _) hCagg_aux) ?_
  rw [show ENNReal.ofReal ((i.fst.val)⁻¹ * Cmu) =
      ENNReal.ofReal (i.fst.val)⁻¹ * ENNReal.ofReal Cmu from
    ENNReal.ofReal_mul hμ_inv_nn]
  rw [show ENNReal.ofReal (Cagg * (i.fst.val)⁻¹ ^ target) =
      ENNReal.ofReal Cagg * ENNReal.ofReal ((i.fst.val)⁻¹ ^ target) from
    ENNReal.ofReal_mul hCagg_nn]
  rw [show ENNReal.ofReal (Cmu * Cagg * (i.fst.val)⁻¹ ^ (target + 1)) =
      ENNReal.ofReal Cmu * ENNReal.ofReal Cagg *
        ENNReal.ofReal ((i.fst.val)⁻¹ ^ target) * ENNReal.ofReal (i.fst.val)⁻¹ by
    rw [show Cmu * Cagg * (i.fst.val)⁻¹ ^ (target + 1) =
        Cmu * Cagg * (i.fst.val)⁻¹ ^ target * (i.fst.val)⁻¹ from by ring,
      ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCmu_nn hCagg_nn) hμ_inv_pow_nn),
      ENNReal.ofReal_mul (mul_nonneg hCmu_nn hCagg_nn),
      ENNReal.ofReal_mul hCmu_nn]]
  ring_nf
  exact le_refl _

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma sharpDiffExplicit_iter_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (j K : ℕ)
    (idx : Fin j → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ j idx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_chart_cpt : MemWkp (d := Module.finrank ℝ E) (K + j) 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
      g r s i (K + j) α P₀
  exact (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
    (I := I) (M := M) g r s i α P₀ j K h_chart_cpt idx).1

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 2000000 in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma eigenvectorChartRHSDiffNumerator_wkpNorm_le_chartcpt_at_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K target : ℕ)
    (l : Fin (m + 1) → Fin (Module.finrank ℝ E))
    (fChartEffPrev : TensorEigenIdx (I := I) (M := M) g r s → EuclN → ℝ)
    (CatomA : ℝ) (hCatomA_nn : 0 ≤ CatomA)
    (hAtomA_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a : Fin (Module.finrank ℝ E)),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CatomA * (i.fst.val)⁻¹ ^ target) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CatomB : ℝ) (hCatomB_nn : 0 ≤ CatomB)
    (hAtomB_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (a b : Fin (Module.finrank ℝ E)),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CatomB * (i.fst.val)⁻¹ ^ target) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CatomC : ℝ) (hCatomC_nn : 0 ≤ CatomC)
    (hAtomC_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CatomC * (i.fst.val)⁻¹ ^ target) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CatomD : ℝ) (hCatomD_nn : 0 ≤ CatomD)
    (hAtomD_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 (fChartEffPrev i)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CatomD * (i.fst.val)⁻¹ ^ target) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (CatomE : ℝ) (hCatomE_nn : 0 ≤ CatomE)
    (hAtomE_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            (fChartEffPrev i)
            (chartTargetEuclid (I := I) (M := M) α))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CatomE * (i.fst.val)⁻¹ ^ target) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i‖)
    (h_prev_mem_succ : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_prev_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      fChartEffPrev i =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
              g r s i α P₀ m l (fChartEffPrev i) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ target) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    sharp_invGramDerivCoeff_mul_iteratedPartial_wkpNorm_le (I := I) (M := M) g r s α P₀ m K l
      CatomA target hCatomA_nn hAtomA_bd
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    sharp_invGramCoeff_mul_iteratedPartialWeakDeriv_wkpNorm_le (I := I) (M := M) g r s α P₀ m K l
      CatomB target hCatomB_nn hAtomB_bd
  obtain ⟨CC, hCC_nn, hCC⟩ :=
    sharp_densityDeriv_mul_iteratedPartial_wkpNorm_le (I := I) (M := M) g r s α P₀ m K l
      CatomC target hCatomC_nn hAtomC_bd
  have h_prev_mem_K : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      MemWkp (d := Module.finrank ℝ E) K 2 (fChartEffPrev i)
        (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    (h_prev_mem_succ i).le_of_le (by omega)
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    sharp_densityDeriv_mul_prevChartFun_wkpNorm_le (I := I) (M := M) g r s α P₀ m K l
      fChartEffPrev h_prev_mem_K h_prev_zero CatomD target hCatomD_nn hAtomD_bd
  obtain ⟨CE, hCE_nn, hCE⟩ :=
    sharp_density_mul_prevChartFunWeakDeriv_wkpNorm_le (I := I) (M := M) g r s α P₀ m K l
      fChartEffPrev h_prev_mem_succ h_prev_zero CatomE target hCatomE_nn hAtomE_bd
  have hCA_prod_nn : 0 ≤ CA * CatomA := mul_nonneg hCA_nn hCatomA_nn
  have hCB_prod_nn : 0 ≤ CB * CatomB := mul_nonneg hCB_nn hCatomB_nn
  have hCC_prod_nn : 0 ≤ CC * CatomC := mul_nonneg hCC_nn hCatomC_nn
  have hCD_prod_nn : 0 ≤ CD * CatomD := mul_nonneg hCD_nn hCatomD_nn
  have hCE_prod_nn : 0 ≤ CE * CatomE := mul_nonneg hCE_nn hCatomE_nn
  refine ⟨CA * CatomA + CB * CatomB + CC * CatomC + CD * CatomD + CE * CatomE,
    by positivity, fun i => ?_⟩
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  set Rhs : ℝ≥0∞ := ENNReal.ofReal
      ‖tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i‖
    with hRhs_def
  set layerA : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      (fderiv ℝ (weightedInvGramDerivOnEuclid (I := I) g α a b
            (l (Fin.last m))) y)
          (EuclideanSpace.single b 1) *
        eigenvectorChartIteratedPartial (I := I) (M := M) g r s i α P₀
          (m + 1) (Fin.cons a (Fin.init l)) y with hlayerA_def
  set layerB : EuclN → ℝ := fun y => ∑ a : Fin (Module.finrank ℝ E),
    ∑ b : Fin (Module.finrank ℝ E),
      weightedInvGramDerivOnEuclid (I := I) g α a b (l (Fin.last m)) y *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α) y with hlayerB_def
  set layerC : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      eigenvectorChartIteratedPartial (I := I) (M := M) g r s i α P₀
        m (Fin.init l) y with hlayerC_def
  set layerD : EuclN → ℝ := fun y =>
    densityDerivOnEuclid (I := I) g α (l (Fin.last m)) y *
      fChartEffPrev i y with hlayerD_def
  set layerE : EuclN → ℝ := fun y =>
    densityOnEuclid (I := I) g α y *
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 (l (Fin.last m))
        (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α) y
    with hlayerE_def
  have h_num_eq : (fun y => eigenvectorChartRHSDiffNumerator (I := I) (M := M)
      g r s i α P₀ m l (fChartEffPrev i) y) =
      fun y => layerA y + layerB y - layerC y + layerD y + layerE y := by
    funext y
    show eigenvectorChartRHSDiffNumerator (I := I) (M := M)
        g r s i α P₀ m l (fChartEffPrev i) y =
      layerA y + layerB y - layerC y + layerD y + layerE y
    rw [hlayerA_def, hlayerB_def, hlayerC_def, hlayerD_def, hlayerE_def,
      eigenvectorChartRHSDiffNumerator]
  have hA_mem : MemWkp (d := Module.finrank ℝ E) K 2 layerA
      (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hlayerA_def]
    refine memWkp_finset_sum (d := Module.finrank ℝ E) hΩ_open
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))) _ (fun a _ => ?_)
    refine memWkp_finset_sum (d := Module.finrank ℝ E) hΩ_open
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))) _ (fun b _ => ?_)
    obtain ⟨_Kc_ab, _hKc_ab_nn, hKc_ab⟩ := sharp_wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K
      (sharpDiffExplicit_layerA_coeff_contDiffOn (I := I) (M := M) g α m l a b)
    exact (hKc_ab _
      (sharpDiffExplicit_iter_memWkp (I := I) (M := M) g r s i α P₀
        (m + 1) K (Fin.cons a (Fin.init l)))
      (eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ (m + 1)
        (Fin.cons a (Fin.init l)))).1
  have hB_mem : MemWkp (d := Module.finrank ℝ E) K 2 layerB
      (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hlayerB_def]
    refine memWkp_finset_sum (d := Module.finrank ℝ E) hΩ_open
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))) _ (fun a _ => ?_)
    refine memWkp_finset_sum (d := Module.finrank ℝ E) hΩ_open
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))) _ (fun b _ => ?_)
    obtain ⟨_Kc_ab, _hKc_ab_nn, hKc_ab⟩ := sharp_wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K
      (weightedInvGramDerivOnEuclid_contDiffOn (I := I) g α a b (l (Fin.last m)))
    have h_chosen_mem : MemWkp (d := Module.finrank ℝ E) K 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 b
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (sharpDiffExplicit_iter_memWkp (I := I) (M := M) g r s i α P₀
        (m + 1) (K + 1) (Fin.cons a (Fin.init l))).chosenWeakPartial_mem b
    have h_chosen_ae_zero :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 b
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
            (chartTargetEuclid (I := I) (M := M) α)
          =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) :=
      chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
        (I := I) (M := M) α
        (eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ (m + 1)
          (Fin.cons a (Fin.init l))) b
    exact (hKc_ab _ h_chosen_mem h_chosen_ae_zero).1
  have hC_mem : MemWkp (d := Module.finrank ℝ E) K 2 layerC
      (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hlayerC_def]
    obtain ⟨_Kc, _hKc_nn, hKc⟩ := sharp_wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    exact (hKc _
      (sharpDiffExplicit_iter_memWkp (I := I) (M := M) g r s i α P₀
        m K (Fin.init l))
      (eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ m (Fin.init l))).1
  have hD_mem : MemWkp (d := Module.finrank ℝ E) K 2 layerD
      (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hlayerD_def]
    obtain ⟨_Kc, _hKc_nn, hKc⟩ := sharp_wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K
      (densityDerivOnEuclid_contDiffOn (I := I) g α (l (Fin.last m)))
    exact (hKc _ (h_prev_mem_K i) (h_prev_zero i)).1
  have hE_mem : MemWkp (d := Module.finrank ℝ E) K 2 layerE
      (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hlayerE_def]
    obtain ⟨_Kc, _hKc_nn, hKc⟩ := sharp_wkpNorm_coef_mul_factor_le_uniform
      (I := I) (M := M) α K (densityOnEuclid_contDiffOn (I := I) g α)
    have h_chosen_mem : MemWkp (d := Module.finrank ℝ E) K 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 (l (Fin.last m))
          (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (h_prev_mem_succ i).chosenWeakPartial_mem (l (Fin.last m))
    have h_chosen_ae_zero :
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 (l (Fin.last m))
            (fChartEffPrev i) (chartTargetEuclid (I := I) (M := M) α)
          =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) :=
      chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
        (I := I) (M := M) α (h_prev_zero i) (l (Fin.last m))
    exact (hKc _ h_chosen_mem h_chosen_ae_zero).1
  have hCA_e : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerA
      (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ target) * Rhs := hCA i
  have hCB_e : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerB
      (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ target) * Rhs := hCB i
  have hCC_e : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerC
      (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ target) * Rhs := hCC i
  have hCD_e : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerD
      (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ target) * Rhs := hCD i
  have hCE_e : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerE
      (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ target) * Rhs := hCE i
  rw [h_num_eq]
  set sAB : EuclN → ℝ := fun y => layerA y + layerB y with hsAB_def
  set sABC : EuclN → ℝ := fun y => sAB y - layerC y with hsABC_def
  set sABCD : EuclN → ℝ := fun y => sABC y + layerD y with hsABCD_def
  have hAB_mem : MemWkp (d := Module.finrank ℝ E) K 2 sAB
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hA_mem hB_mem
  have hABC_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABC
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp.sub (d := Module.finrank ℝ E) (by norm_num) hΩ_open hAB_mem hC_mem
  have hABCD_mem : MemWkp (d := Module.finrank ℝ E) K 2 sABCD
      (chartTargetEuclid (I := I) (M := M) α) :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open hABC_mem hD_mem
  have h_sAB_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sAB
      (chartTargetEuclid (I := I) (M := M) α) ≤
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerA
          (chartTargetEuclid (I := I) (M := M) α)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerB
          (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open hA_mem hB_mem
  have h_sABC_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABC
      (chartTargetEuclid (I := I) (M := M) α) ≤
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sAB
          (chartTargetEuclid (I := I) (M := M) α)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerC
          (chartTargetEuclid (I := I) (M := M) α) :=
    sharpDiffExplicit_wkpNorm_sub_le hΩ_open hAB_mem hC_mem
  have h_sABCD_le : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABCD
      (chartTargetEuclid (I := I) (M := M) α) ≤
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABC
          (chartTargetEuclid (I := I) (M := M) α)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerD
          (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open hABC_mem hD_mem
  have h_split : (fun y => layerA y + layerB y - layerC y + layerD y
        + layerE y) = (fun y => sABCD y + layerE y) := by
    funext y
    rw [hsABCD_def, hsABC_def, hsAB_def]
  have h_tri :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
          (fun y => layerA y + layerB y - layerC y + layerD y + layerE y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerA
            (chartTargetEuclid (I := I) (M := M) α)
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerB
            (chartTargetEuclid (I := I) (M := M) α)
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerC
            (chartTargetEuclid (I := I) (M := M) α)
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerD
            (chartTargetEuclid (I := I) (M := M) α)
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerE
            (chartTargetEuclid (I := I) (M := M) α) := by
    rw [h_split]
    have h_outer : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
        (fun y => sABCD y + layerE y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 sABCD
            (chartTargetEuclid (I := I) (M := M) α)
          + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerE
            (chartTargetEuclid (I := I) (M := M) α) :=
      wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        hABCD_mem hE_mem
    refine le_trans h_outer ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans h_sABCD_le ?_
    refine add_le_add ?_ (le_refl _)
    refine le_trans h_sABC_le ?_
    refine add_le_add ?_ (le_refl _)
    exact h_sAB_le
  refine le_trans h_tri ?_
  have h_five :
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerA
          (chartTargetEuclid (I := I) (M := M) α)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerB
          (chartTargetEuclid (I := I) (M := M) α)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerC
          (chartTargetEuclid (I := I) (M := M) α)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerD
          (chartTargetEuclid (I := I) (M := M) α)
        + iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 layerE
          (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ target) * Rhs +
        ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ target) * Rhs +
        ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ target) * Rhs +
        ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ target) * Rhs +
        ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ target) * Rhs :=
    add_le_add (add_le_add (add_le_add (add_le_add hCA_e hCB_e) hCC_e) hCD_e)
      hCE_e
  refine le_trans h_five ?_
  set μi : ℝ := (i.fst.val)⁻¹ ^ target with hμi_def
  have hμi_nn : 0 ≤ μi := by
    rw [hμi_def]
    have h1 : 1 ≤ (i.fst.val)⁻¹ :=
      sharpDiff_eigen_inv_one_le (I := I) (M := M) g r s i
    have : 0 ≤ (i.fst.val)⁻¹ := le_trans zero_le_one h1
    exact pow_nonneg this _
  have h_pull :
      ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ target) * Rhs +
        ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ target) * Rhs +
        ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ target) * Rhs +
        ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ target) * Rhs +
        ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ target) * Rhs
        = ENNReal.ofReal ((CA * CatomA + CB * CatomB + CC * CatomC +
            CD * CatomD + CE * CatomE) * (i.fst.val)⁻¹ ^ target) * Rhs := by
    have hp1 : 0 ≤ CA * CatomA + CB * CatomB := add_nonneg hCA_prod_nn hCB_prod_nn
    have hp2 : 0 ≤ CA * CatomA + CB * CatomB + CC * CatomC :=
      add_nonneg hp1 hCC_prod_nn
    have hp3 : 0 ≤ CA * CatomA + CB * CatomB + CC * CatomC + CD * CatomD :=
      add_nonneg hp2 hCD_prod_nn
    have h_sum_ofReal :
        ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ target) +
          ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ target) +
          ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ target) +
          ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ target) +
          ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ target)
          = ENNReal.ofReal ((CA * CatomA + CB * CatomB + CC * CatomC +
              CD * CatomD + CE * CatomE) * (i.fst.val)⁻¹ ^ target) := by
      rw [add_mul, add_mul, add_mul, add_mul,
        ENNReal.ofReal_add (by positivity) (mul_nonneg hCE_prod_nn hμi_nn),
        ENNReal.ofReal_add (by positivity) (mul_nonneg hCD_prod_nn hμi_nn),
        ENNReal.ofReal_add (by positivity) (mul_nonneg hCC_prod_nn hμi_nn),
        ENNReal.ofReal_add (mul_nonneg hCA_prod_nn hμi_nn)
          (mul_nonneg hCB_prod_nn hμi_nn)]
    calc ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ target) * Rhs +
            ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ target) * Rhs +
            ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ target) * Rhs +
            ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ target) * Rhs +
            ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ target) * Rhs
        = (ENNReal.ofReal (CA * CatomA * (i.fst.val)⁻¹ ^ target) +
            ENNReal.ofReal (CB * CatomB * (i.fst.val)⁻¹ ^ target) +
            ENNReal.ofReal (CC * CatomC * (i.fst.val)⁻¹ ^ target) +
            ENNReal.ofReal (CD * CatomD * (i.fst.val)⁻¹ ^ target) +
            ENNReal.ofReal (CE * CatomE * (i.fst.val)⁻¹ ^ target)) * Rhs := by
          rw [add_mul, add_mul, add_mul, add_mul]
      _ = ENNReal.ofReal ((CA * CatomA + CB * CatomB + CC * CatomC +
              CD * CatomD + CE * CatomE) * (i.fst.val)⁻¹ ^ target) * Rhs := by
          rw [h_sum_ofReal]
  rw [h_pull]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma sharpDiffExplicit_diff_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (N : ℕ)
    (H : eigenvectorChartRHSDiffSharpWkpBoundsUpToOrder (I := I) (M := M) g r s α P₀ N)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (m K' : ℕ) (hN : m + 1 + K' ≤ N) (l : Fin m → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartRHSDiff (I := I) (M := M) g r s i α P₀ m l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartRHSDiff_memWkp (I := I) (M := M) g r s i α P₀
    m K' l (fun β Q => H.h_pou_resolv i (m + 1 + K') β Q hN)

set_option maxHeartbeats 32000000 in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma sharpDiffBdd_recursion_at_target
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (N eAtomMax : ℕ)
    (H : eigenvectorChartRHSDiffSharpWkpBoundsUpToOrder (I := I) (M := M) g r s α P₀ N)
    (h_atom_bd : ∀ K', K' ≤ N →
      H.eEig K' ≤ eAtomMax ∧ H.eResH K' ≤ eAtomMax ∧
        H.eResL K' ≤ eAtomMax ∧ H.ePar K' ≤ eAtomMax ∧
        H.eCom K' ≤ eAtomMax ∧ H.eCcR K' ≤ eAtomMax ∧
        H.eCcut K' ≤ eAtomMax) :
    ∀ (m : ℕ) (K : ℕ) (_ : K + m + 1 ≤ N)
      (l : Fin m → Fin (Module.finrank ℝ E)),
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartRHSDiff (I := I) (M := M)
                g r s i α P₀ m l)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (eAtomMax + 1)) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M)
                    g r s) i‖ := by
  classical
  intro m
  induction m with
  | zero =>
      intro K hKN _l
      have hK1_le_N : K + 1 ≤ N := by simpa using hKN
      have hAt := h_atom_bd K (by omega)
      obtain ⟨C, hC_nn, hC_bd⟩ :=
        sharpDiffBdd_level_zero_wkpNorm_at_target (I := I) (M := M)
          g r s α P₀ K N eAtomMax hK1_le_N H
          hAt.1 hAt.2.1 hAt.2.2.1 hAt.2.2.2.1
          hAt.2.2.2.2.1 hAt.2.2.2.2.2.1 hAt.2.2.2.2.2.2
      refine ⟨C, hC_nn, fun i => ?_⟩
      rw [eigenvectorChartRHSDiff_zero (I := I) (M := M)
        g r s i α P₀ _l]
      exact hC_bd i
  | succ m ih =>
      intro K hKN l
      have hKN_K : K + m + 1 ≤ N := by omega
      have hKN_K1 : (K + 1) + m + 1 ≤ N := by omega
      obtain ⟨C_K, hC_K_nn, hC_K_bd⟩ := ih K hKN_K (Fin.init l)
      obtain ⟨C_K1, hC_K1_nn, hC_K1_bd⟩ := ih (K + 1) hKN_K1 (Fin.init l)
      have hKN_diff : m + 1 + (K + 1) ≤ N := by omega
      have h_prev_mem_succ : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m (Fin.init l))
            (chartTargetEuclid (I := I) (M := M) α) := fun i =>
        sharpDiffExplicit_diff_memWkp (I := I) (M := M) g r s α P₀ N
          H i m (K + 1) hKN_diff (Fin.init l)
      have h_prev_ae_zero : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
          eigenvectorChartRHSDiff (I := I) (M := M) g r s i α P₀ m
              (Fin.init l)
            =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α \
                chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)) :=
        fun i =>
          eigenvectorChartRHSDiff_ae_zero_off_chartPouKernel
            (I := I) (M := M) g r s i α P₀ m (Fin.init l)
      have hKN_KmP1 : K + m + 1 ≤ N := hKN_K
      have hAtomA_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (a : Fin (Module.finrank ℝ E)),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.Ceig (K + m + 1) *
              (i.fst.val)⁻¹ ^ (eAtomMax + 1)) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖ := by
        intro i a
        have h_chart_cpt_mem :
            MemWkp (d := Module.finrank ℝ E) (K + (m + 1)) 2
              (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
                g r s i α P₀)
              (chartTargetEuclid (I := I) (M := M) α) :=
          eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
            g r s i (K + (m + 1)) α P₀
        have h_bridge :=
          (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
            (I := I) (M := M) g r s i α P₀ (m + 1) K
            h_chart_cpt_mem
            (Fin.cons a (Fin.init l))).2
        refine le_trans h_bridge ?_
        have h_eig := H.hCeig_bd i (K + (m + 1)) (by omega)
        have h_arith : K + m + 1 = K + (m + 1) := by ring
        rw [h_arith]
        refine le_trans h_eig ?_
        refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
        exact sharpDiff_ofReal_const_pow_eigen_inv_le
          (I := I) (M := M) g r s i (H.hCeig_nn _)
          (le_trans (h_atom_bd (K + (m + 1)) (by omega)).1 (Nat.le_succ _))
      have hAtomB_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (a b : Fin (Module.finrank ℝ E)),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 b
                (eigenvectorChartIteratedPartial (I := I) (M := M)
                  g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l)))
                (chartTargetEuclid (I := I) (M := M) α))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.Ceig (K + m + 2) *
              (i.fst.val)⁻¹ ^ (eAtomMax + 1)) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖ := by
        intro i a b
        have h_chosen := wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
          (p := 2) K
          (chartTargetEuclid_isOpen (I := I) (M := M) α)
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s i α P₀ (m + 1) (Fin.cons a (Fin.init l))) b
        refine le_trans h_chosen ?_
        have h_chart_cpt_mem :
            MemWkp (d := Module.finrank ℝ E) ((K + 1) + (m + 1)) 2
              (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
                g r s i α P₀)
              (chartTargetEuclid (I := I) (M := M) α) :=
          eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
            g r s i ((K + 1) + (m + 1)) α P₀
        have h_bridge :=
          (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
            (I := I) (M := M) g r s i α P₀ (m + 1) (K + 1)
            h_chart_cpt_mem
            (Fin.cons a (Fin.init l))).2
        refine le_trans h_bridge ?_
        have h_eig := H.hCeig_bd i ((K + 1) + (m + 1)) (by omega)
        have h_arith : K + m + 2 = (K + 1) + (m + 1) := by ring
        rw [h_arith]
        refine le_trans h_eig ?_
        refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
        exact sharpDiff_ofReal_const_pow_eigen_inv_le
          (I := I) (M := M) g r s i (H.hCeig_nn _)
          (le_trans (h_atom_bd ((K + 1) + (m + 1)) (by omega)).1 (Nat.le_succ _))
      have hAtomC_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s i α P₀ m (Fin.init l))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (H.Ceig (K + m) *
              (i.fst.val)⁻¹ ^ (eAtomMax + 1)) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖ := by
        intro i
        have h_chart_cpt_mem :
            MemWkp (d := Module.finrank ℝ E) (K + m) 2
              (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
                g r s i α P₀)
              (chartTargetEuclid (I := I) (M := M) α) :=
          eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
            g r s i (K + m) α P₀
        have h_bridge :=
          (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
            (I := I) (M := M) g r s i α P₀ m K
            h_chart_cpt_mem
            (Fin.init l)).2
        refine le_trans h_bridge ?_
        refine le_trans (H.hCeig_bd i (K + m) (by omega)) ?_
        refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
        exact sharpDiff_ofReal_const_pow_eigen_inv_le
          (I := I) (M := M) g r s i (H.hCeig_nn _)
          (le_trans (h_atom_bd (K + m) (by omega)).1 (Nat.le_succ _))
      have hAtomD_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (eigenvectorChartRHSDiff (I := I) (M := M)
                g r s i α P₀ m (Fin.init l))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (C_K * (i.fst.val)⁻¹ ^ (eAtomMax + 1)) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖ := hC_K_bd
      have hAtomE_bd : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
          iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 (l (Fin.last m))
                (eigenvectorChartRHSDiff (I := I) (M := M)
                  g r s i α P₀ m (Fin.init l))
                (chartTargetEuclid (I := I) (M := M) α))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (C_K1 * (i.fst.val)⁻¹ ^ (eAtomMax + 1)) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec
                  (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator
                    (I := I) (M := M) g r s) i‖ := by
        intro i
        have h_chosen := wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
          (p := 2) K
          (chartTargetEuclid_isOpen (I := I) (M := M) α)
          (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m (Fin.init l)) (l (Fin.last m))
        exact le_trans h_chosen (hC_K1_bd i)
      obtain ⟨Cnum, hCnum_nn, hCnum_bd⟩ :=
        eigenvectorChartRHSDiffNumerator_wkpNorm_le_chartcpt_at_target
          (I := I) (M := M) g r s α P₀ m K (eAtomMax + 1) l
          (fun i => eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (H.Ceig (K + m + 1)) (H.hCeig_nn _) hAtomA_bd
          (H.Ceig (K + m + 2)) (H.hCeig_nn _) hAtomB_bd
          (H.Ceig (K + m)) (H.hCeig_nn _) hAtomC_bd
          C_K hC_K_nn hAtomD_bd
          C_K1 hC_K1_nn hAtomE_bd
          h_prev_mem_succ h_prev_ae_zero
      obtain ⟨Cden, hCden_nn, hCden_bd⟩ :=
        sharpDiff_wkpNorm_coef_mul_factor_le_uniform (I := I) (M := M) α K
          (one_div_densityOnEuclid_contDiffOn_chartTargetEuclid
            (I := I) (M := M) g α)
      refine ⟨Cden * Cnum, mul_nonneg hCden_nn hCnum_nn, fun i => ?_⟩
      set numFun : EuclN → ℝ :=
        eigenvectorChartRHSDiffNumerator (I := I) (M := M)
          g r s i α P₀ m l
          (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s i α P₀ m (Fin.init l)) with hnumFun_def
      set Q : EuclN → ℝ := fun y =>
        (1 / densityOnEuclid (I := I) g α y) * numFun y with hQ_def
      have h_num_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 numFun
          (chartTargetEuclid (I := I) (M := M) α) := by
        rw [hnumFun_def]
        refine eigenvectorChartRHSDiffNumerator_memWkp_of_iter
          (I := I) (M := M) g r s i α P₀ m K l ?_ ?_ ?_
        · intro j idx
          have h_chart_cpt_mem :
              MemWkp (d := Module.finrank ℝ E) ((2 + K) + j) 2
                (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
                  g r s i α P₀)
                (chartTargetEuclid (I := I) (M := M) α) :=
            eigenvector_chartComponent_memWkp_arbitrary (I := I) (M := M)
              g r s i ((2 + K) + j) α P₀
          exact (eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
            (I := I) (M := M) g r s i α P₀ j (2 + K)
            h_chart_cpt_mem idx).1
        · exact h_prev_mem_succ i
        · exact h_prev_ae_zero i
      have h_num_ae_zero :
          numFun =ᵐ[(volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α \
              chartPouKernel (I := I) (M := M) α)]
            (fun _ : EuclN => (0 : ℝ)) := by
        rw [hnumFun_def]
        exact eigenvectorChartRHSDiffNumerator_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s i α P₀ m l (h_prev_ae_zero i)
      have h_Q_props := hCden_bd numFun h_num_memWkp h_num_ae_zero
      have h_Q_bd : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 Q
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal Cden *
            iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 numFun
              (chartTargetEuclid (I := I) (M := M) α) := h_Q_props.2
      have h_Q_ae_zero : Q =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartPouKernel (I := I) (M := M) α)]
          (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_num_ae_zero] with y hy
        rw [hQ_def]
        simp [hy]
      have h_diff_eq : eigenvectorChartRHSDiff (I := I) (M := M)
          g r s i α P₀ (m + 1) l =
          Set.indicator (chartPouKernel (I := I) (M := M) α) Q := by
        rw [eigenvectorChartRHSDiff_succ]
        funext y
        rw [hQ_def, hnumFun_def]
        rcases Classical.em (y ∈ chartPouKernel (I := I) (M := M) α) with
          h_mem | h_mem
        · rw [Set.indicator_of_mem h_mem, Set.indicator_of_mem h_mem,
            one_div, mul_comm, ← div_eq_mul_inv]
        · rw [Set.indicator_of_notMem h_mem, Set.indicator_of_notMem h_mem]
      rw [h_diff_eq]
      have h_strip := sharpDiff_wkpNorm_indicator_eq (I := I) (M := M) α K
        (Q := Q) h_Q_ae_zero
      rw [h_strip]
      have hCnum_bd_i : iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2 numFun
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal (Cnum * (i.fst.val)⁻¹ ^ (eAtomMax + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ := by
        rw [hnumFun_def]
        exact hCnum_bd i
      refine le_trans h_Q_bd ?_
      refine le_trans (mul_le_mul' (le_refl _) hCnum_bd_i) ?_
      have hμ_inv_pow_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ ^ (eAtomMax + 1) := by
        exact pow_nonneg (sharpDiff_eigen_inv_nn
          (I := I) (M := M) g r s i) _
      rw [show ENNReal.ofReal (Cnum * (i.fst.val)⁻¹ ^ (eAtomMax + 1)) =
          ENNReal.ofReal Cnum * ENNReal.ofReal ((i.fst.val)⁻¹ ^ (eAtomMax + 1))
          from ENNReal.ofReal_mul hCnum_nn]
      rw [show ENNReal.ofReal (Cden * Cnum * (i.fst.val)⁻¹ ^ (eAtomMax + 1)) =
          ENNReal.ofReal Cden * ENNReal.ofReal Cnum *
            ENNReal.ofReal ((i.fst.val)⁻¹ ^ (eAtomMax + 1)) by
        rw [ENNReal.ofReal_mul (mul_nonneg hCden_nn hCnum_nn),
          ENNReal.ofReal_mul hCden_nn]]
      ring_nf
      exact le_refl _

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorChartRHSDiff_wkpNorm_le_chartcpt_sharp_bdd_explicit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (H : eigenvectorChartRHSDiffSharpWkpBoundsUpToOrder (I := I) (M := M) g r s α P₀ (K + m + 1))
    (eAtomMax : ℕ)
    (h_eAtomMax_ge : ∀ K', K' ≤ K + m + 1 →
      H.eEig K' ≤ eAtomMax ∧ H.eResH K' ≤ eAtomMax ∧
        H.eResL K' ≤ eAtomMax ∧ H.ePar K' ≤ eAtomMax ∧
        H.eCom K' ≤ eAtomMax ∧ H.eCcR K' ≤ eAtomMax ∧
        H.eCcut K' ≤ eAtomMax) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) K 2
            (eigenvectorChartRHSDiff (I := I) (M := M)
              g r s i α P₀ m l)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (C * (i.fst.val)⁻¹ ^ (eAtomMax + 1)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i‖ :=
  sharpDiffBdd_recursion_at_target (I := I) (M := M) g r s α P₀
    (K + m + 1) eAtomMax H h_eAtomMax_ge m K (le_refl _) l

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
