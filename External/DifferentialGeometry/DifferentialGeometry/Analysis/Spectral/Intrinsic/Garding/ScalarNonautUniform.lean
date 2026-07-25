import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarFluxJetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ParametricPairing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarGalerkinPairing
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField








noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem appRS_jet_bdd
    (q : SmoothRiemannianMetric I M) {alpha : Type*} {p a b : ℕ}
    (Phi : alpha → SmoothCcTensor q a b) (W : alpha → SmoothCcTensor q p a)
    (A : Set alpha) (BPhi BW : ℕ → ℝ)
    (hBPhi : ∀ i, 0 ≤ BPhi i) (hBW : ∀ i, 0 ≤ BW i)
    (hPhi : ∀ i t, t ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q a (b + i) x
        ((iteratedCovGrad (I := I) q a b i (Phi t)).toSection x) ≤ BPhi i)
    (hW : ∀ i t, t ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q p (a + i) x
        ((iteratedCovGrad (I := I) q p a i (W t)).toSection x) ≤ BW i) :
    ∃ D : ℕ → ℝ, (∀ i, 0 ≤ D i) ∧
      ∀ i t, t ∈ A → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) q p (b + i) x
          ((iteratedCovGrad (I := I) q p b i
            (ccOperatorFieldComp (I := I) (M := M) q p a b (Phi t) (W t))).toSection x) ≤ D i := by
  classical
  let D : ℕ → ℝ := fun j => diagonalGridGrowthFactor (E := E) j *
    ∑ i ∈ Finset.range (j + 1), BPhi i *
      ∑ l ∈ Finset.range (j + 1 - i), BW l
  refine ⟨D, fun j => mul_nonneg (appCcGdiag_nonneg (E := E) j)
    (Finset.sum_nonneg fun i _ => mul_nonneg (hBPhi i)
      (Finset.sum_nonneg fun l _ => hBW l)), ?_⟩
  intro j t ht x
  refine (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) q j p a b (Phi t) (W t) x).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) j)
  refine Finset.sum_le_sum (fun i _ => ?_)
  have hleft := hPhi i t ht x
  have hright :
      (∑ l ∈ Finset.range (j + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) q p (a + l) x
          ((iteratedCovGrad (I := I) q p a l (W t)).toSection x)) ≤
        ∑ l ∈ Finset.range (j + 1 - i), BW l := by
    exact Finset.sum_le_sum (fun l _ => hW l t ht x)
  exact mul_le_mul hleft hright
    (Finset.sum_nonneg fun l _ =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) q p (a + l) x _)
    (hBPhi i)

omit [NeZero (Module.finrank ℝ E)] in
private theorem fixed_jet_bdd
    (q : SmoothRiemannianMetric I M) {r s : ℕ} (Phi : SmoothCcTensor q r s) :
    ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧ ∀ i x,
      riemannianFiberNormSq (I := I) (M := M) q r (s + i) x
        ((iteratedCovGrad (I := I) q r s i Phi).toSection x) ≤ B i := by
  let P : ℝ → SmoothCcTensor q r s := fun _ => Phi
  have hPjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) p.1
        ((P p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ (Set.univ : Set ℝ)) := by
    simpa only [P] using
      Phi.toSection.contMDiff.comp_contMDiffOn contMDiffOn_fst
  obtain ⟨B, hB, hjet⟩ :=
    joint_jet_bdd (I := I) (M := M) q r s P
      (K := ({0} : Set ℝ)) (S := Set.univ) isCompact_singleton
      (by simp only [Set.singleton_subset_iff, Set.mem_univ]) hPjoint
  refine ⟨B, hB, fun i x => ?_⟩
  simpa only [P] using hjet i 0 (Set.mem_singleton 0) x

private lemma grid_mono {a b : ℕ → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j ≤ b j) (i : ℕ) :
    DifferentialGeometry.Combinatorics.antidiagonalTupleGrid a i ≤
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid b i := by
  classical
  rw [DifferentialGeometry.Combinatorics.antidiagonalTupleGrid,
    DifferentialGeometry.Combinatorics.antidiagonalTupleGrid]
  refine Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun e _ => ?_))
  exact Finset.prod_le_prod (fun m _ => ha (e m)) (fun m _ => hab (e m))

private theorem flux_jet_of_bdd
    (q : SmoothRiemannianMetric I M) {alpha : Type*}
    (h : alpha → SmoothRiemannianMetric I M)
    (P : alpha → SmoothCcTensor q 0 2) (A : Set alpha)
    (J : ℕ → ℝ) (hJ_nn : ∀ i, 0 ≤ J i)
    (htie : ∀ t, t ∈ A → ∀ y v w,
      (h t).inner y v w = q.inner y v w +
        ccTensorBilinSymm (I := I) q (P t) y v w)
    (hsmall : ∀ t, t ∈ A →
      metricCauchySchwarzBound (I := I) q (ccTensorBilinSymm (I := I) q (P t)) (1 / 4 : ℝ))
    (hP : ∀ i t, t ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 0 (2 + i) x
        ((iteratedCovGrad (I := I) q 0 2 i (P t)).toSection x) ≤ J i) :
    ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
      ∀ i t, t ∈ A → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) q 1 (1 + i) x
          ((iteratedCovGrad (I := I) q 1 1 i
            (scalarFluxCoeff (I := I) q (h t))).toSection x) ≤ B i := by
  obtain ⟨C, hC_nn, hC⟩ :=
    scalarFlux_jet_grid (I := I) (M := M) q (by norm_num : (1 / 2 : ℝ) < 1)
  let B : ℕ → ℝ := fun i => C i *
    DifferentialGeometry.Combinatorics.antidiagonalTupleGrid J i
  refine ⟨B, fun i => mul_nonneg (hC_nn i)
    (DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_nonneg J hJ_nn i), ?_⟩
  intro i t ht x
  have hlocal := hC (h t) (P t) (htie t ht)
    (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (hsmall t ht) i x
  have hgrid :
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid
          (fun j => riemannianFiberNormSq (I := I) (M := M) q 0 (2 + j) x
            ((iteratedCovGrad (I := I) q 0 2 j (P t)).toSection x)) i ≤
        DifferentialGeometry.Combinatorics.antidiagonalTupleGrid J i := by
    exact grid_mono
      (fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) q 0 (2 + j) x _)
      (fun j => hP j t ht x) i
  exact hlocal.trans (mul_le_mul_of_nonneg_left hgrid (hC_nn i))

private theorem fluxDiv_jet_bdd
    (q : SmoothRiemannianMetric I M) {α : Type*}
    (C : α → SmoothCcTensor q 1 1) (A : Set α)
    (B : ℕ → ℝ) (hB_nn : ∀ i, 0 ≤ B i)
    (hB : ∀ i t, t ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 1 (1 + i) x
        ((iteratedCovGrad (I := I) q 1 1 i (C t)).toSection x) ≤ B i) :
    ∃ D : ℕ → ℝ, (∀ i, 0 ≤ D i) ∧
      ∀ i t, t ∈ A → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) q 1 (0 + i) x
          ((iteratedCovGrad (I := I) q 1 0 i
            (ccOperatorFieldComp (I := I) (M := M) q 1 2 0
              (cometricDoubleTraceField (I := I) q 0)
              (covGrad (I := I) (M := M) q 1 1 (C t)))).toSection x) ≤ D i := by
  obtain ⟨F, hF_nn, hF⟩ := fixed_jet_bdd (I := I) (M := M) q
    (cometricDoubleTraceField (I := I) q 0)
  let Q : α → SmoothCcTensor q 2 0 := fun _ =>
    cometricDoubleTraceField (I := I) q 0
  let W : α → SmoothCcTensor q 1 2 := fun t =>
    covGrad (I := I) (M := M) q 1 1 (C t)
  have hQ : ∀ i t, t ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 2 (0 + i) x
        ((iteratedCovGrad (I := I) q 2 0 i (Q t)).toSection x) ≤ F i := by
    intro i t ht x
    simpa only [Q] using hF i x
  have hW : ∀ i t, t ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 1 (2 + i) x
        ((iteratedCovGrad (I := I) q 1 2 i (W t)).toSection x) ≤ B (i + 1) := by
    intro i t ht x
    simp only [W]
    rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M)]
    exact hB (i + 1) t ht x
  obtain ⟨D, hD_nn, hD⟩ := appRS_jet_bdd (I := I) (M := M) q Q W A F
    (fun i => B (i + 1)) hF_nn (fun i => hB_nn (i + 1)) hQ hW
  refine ⟨D, hD_nn, fun i t ht x => ?_⟩
  simpa only [Q, W] using hD i t ht x

private theorem traceCast_jet_bdd
    (q : SmoothRiemannianMetric I M) {alpha : Type*}
    (h : alpha → SmoothRiemannianMetric I M) (A : Set alpha)
    (B : ℕ → ℝ) (hB_nn : ∀ i, 0 ≤ B i)
    (hB : ∀ i t, t ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 1 (1 + i) x
        ((iteratedCovGrad (I := I) q 1 1 i
          (scalarFluxCoeff (I := I) q (h t))).toSection x) ≤ B i) :
    ∃ R D : ℕ → ℝ, (∀ i, 0 ≤ R i) ∧ (∀ i, 0 ≤ D i) ∧
      (∀ i t, t ∈ A → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) q 2 (0 + i) x
          ((iteratedCovGrad (I := I) q 2 0 i
            (scalarTraceCoeff (I := I) q (h t))).toSection x) ≤ R i) ∧
      ∀ i t, t ∈ A → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) q 2 (0 + i) x
          ((iteratedCovGrad (I := I) q 2 0 i
            (traceCast (I := I) q (h t))).toSection x) ≤ D i := by
  classical
  obtain ⟨F, hF_nn, hF⟩ := fixed_jet_bdd (I := I) (M := M) q
    (cometricDoubleTraceField (I := I) q 0)
  let Q : alpha → SmoothCcTensor q 2 0 := fun _ =>
    cometricDoubleTraceField (I := I) q 0
  let S : alpha → SmoothCcTensor q 2 2 := fun t =>
    slotExtend (I := I) (M := M) q 1 1
      (scalarFluxCoeff (I := I) q (h t))
  let BS : ℕ → ℝ := fun i => (Module.finrank ℝ E : ℝ) * B i
  have hQ : ∀ i t, t ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 2 (0 + i) x
        ((iteratedCovGrad (I := I) q 2 0 i (Q t)).toSection x) ≤ F i := by
    intro i t ht x
    simpa only [Q] using hF i x
  have hBS_nn : ∀ i, 0 ≤ BS i := fun i =>
    mul_nonneg (Nat.cast_nonneg _) (hB_nn i)
  have hS : ∀ i t, t ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 2 (2 + i) x
        ((iteratedCovGrad (I := I) q 2 2 i (S t)).toSection x) ≤ BS i := by
    intro i t ht x
    simpa only [S, BS] using
      (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) q 1 1
        (scalarFluxCoeff (I := I) q (h t)) i x).trans
          (mul_le_mul_of_nonneg_left (hB i t ht x) (Nat.cast_nonneg _))
  obtain ⟨R, hR_nn, hR⟩ := appRS_jet_bdd (I := I) (M := M) q Q S A F BS
    hF_nn hBS_nn hQ hS
  let D : ℕ → ℝ := fun i => 2 * R i + 2 * F i
  have hscalar : ∀ i t, t ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 2 (0 + i) x
          ((iteratedCovGrad (I := I) q 2 0 i
            (scalarTraceCoeff (I := I) q (h t))).toSection x) ≤ R i := by
    intro i t ht x
    simpa only [Q, S, scalar_trace_factor] using hR i t ht x
  refine ⟨R, D, hR_nn, fun i => add_nonneg (mul_nonneg (by norm_num) (hR_nn i))
    (mul_nonneg (by norm_num) (hF_nn i)), hscalar, ?_⟩
  intro i t ht x
  have hcast : traceCast (I := I) q (h t) =
      scalarTraceCoeff (I := I) q (h t) +
        cometricDoubleTraceField (I := I) q 0 := by
    rw [scalarTraceCoeff]
    abel
  rw [hcast, iteratedCovGrad_add]
  have hsplit :
      ((iteratedCovGrad (I := I) q 2 0 i
          (scalarTraceCoeff (I := I) q (h t)) +
        iteratedCovGrad (I := I) q 2 0 i
          (cometricDoubleTraceField (I := I) q 0)).toSection x) =
        (iteratedCovGrad (I := I) q 2 0 i
          (scalarTraceCoeff (I := I) q (h t))).toSection x +
        (iteratedCovGrad (I := I) q 2 0 i
          (cometricDoubleTraceField (I := I) q 0)).toSection x := by
    rw [SmoothCcTensor.toSection_add]
    rfl
  rw [hsplit]
  exact (riemannianFiberNormSq_add_le (I := I) (M := M) q 2 (0 + i) x _ _).trans
    (add_le_add (mul_le_mul_of_nonneg_left (hscalar i t ht x) (by norm_num))
      (mul_le_mul_of_nonneg_left (hF i x) (by norm_num)))



theorem cc_comm_unif
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ s ∈ Set.Icc (0 : ℝ) tau, ∀ U : SmoothCcTensor (G.metric (T : ℝ)) 0 0,
          |tensorL2Inner (I := I) (M := M) (G.metric (T : ℝ)) 0 0
              (oneMinusConnLapSmoothIter (I := I) (G.metric (T : ℝ)) 0 0 n U).toFun
              (operatorFieldApply (I := I) (M := M) (G.metric (T : ℝ)) 2 0
                (scalarTraceCoeff (I := I) (G.metric (T : ℝ))
                  (G.metric ((T : ℝ) - s)))
                (iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 2 U)).toFun +
            tensorL2Inner (I := I) (M := M) (G.metric (T : ℝ)) 0 (1 + n)
              (iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 1 n
                (covGrad (I := I) (M := M) (G.metric (T : ℝ)) 0 0 U)).toFun
              (ccOperatorFieldComp (I := I) (M := M) (G.metric (T : ℝ)) 0 (1 + n) (1 + n)
                (slotExtendIter (I := I) (M := M) (G.metric (T : ℝ)) 1 1 n
                  (scalarFluxCoeff (I := I) (G.metric (T : ℝ))
                    (G.metric ((T : ℝ) - s))))
                (iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 1 n
                  (covGrad (I := I) (M := M) (G.metric (T : ℝ)) 0 0 U))).toFun| ≤
            C * ((∑ j ∈ Finset.range (n + 1),
                ‖iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 j U‖) *
              (∑ j ∈ Finset.range (n + 2),
                ‖iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 j U‖)) := by
  classical
  obtain ⟨tau, htau, htau_one, B, hB_nn, hB⟩ :=
    scalarFlux_slab (I := I) (M := M) G hG T
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let A : Set ℝ := Set.Icc (0 : ℝ) tau
  let C₀ : ℝ → SmoothCcTensor q 1 1 := fun s =>
    scalarFluxCoeff (I := I) q (G.metric ((T : ℝ) - s))
  let Φ : ℝ → SmoothCcTensor q 1 0 := fun s =>
    ccOperatorFieldComp (I := I) (M := M) q 1 2 0
      (cometricDoubleTraceField (I := I) q 0)
      (covGrad (I := I) (M := M) q 1 1 (C₀ s))
  have hC₀ : ∀ i s, s ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 1 (1 + i) x
        ((iteratedCovGrad (I := I) q 1 1 i (C₀ s)).toSection x) ≤ B i := by
    intro i s hs x
    simpa only [q, A, C₀] using hB s hs i x
  obtain ⟨D₀, hD₀_nn, hD₀⟩ :=
    fluxDiv_jet_bdd (I := I) (M := M) q C₀ A B hB_nn hC₀
  have hΦ : ∀ i s, s ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 1 (0 + i) x
        ((iteratedCovGrad (I := I) q 1 0 i (Φ s)).toSection x) ≤ D₀ i := by
    simpa only [Φ] using hD₀
  obtain ⟨CG, hCG_nn, hCG⟩ :=
    app_jet_of_bdd (I := I) (M := M) q 1 0 Φ A D₀ hD₀_nn hΦ
  refine ⟨tau, htau, htau_one, fun n => ?_⟩
  obtain ⟨Ct, hCt_nn, hCt⟩ :=
    slot_iterL_unif (I := I) (M := M) q 0 n C₀ A B hB_nn hC₀
  obtain ⟨Cd, hCd_nn, hCd⟩ :=
    iterL_pair_jet_of (I := I) (M := M) q 0 n Φ A CG hCG_nn hCG
  refine ⟨Ct + Cd, add_nonneg hCt_nn hCd_nn, ?_⟩
  intro s hs U
  let P : ℝ := tensorL2Inner (I := I) (M := M) q 0 0
    (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
    (operatorFieldApply (I := I) (M := M) q 2 0
      (scalarTraceCoeff (I := I) q (G.metric ((T : ℝ) - s)))
      (iteratedCovGrad (I := I) q 0 0 2 U)).toFun
  let G₀ : ℝ := tensorL2Inner (I := I) (M := M) q 0 1
    (covGrad (I := I) (M := M) q 0 0
      (oneMinusConnLapSmoothIter (I := I) q 0 0 n U)).toFun
    (operatorFieldApply (I := I) (M := M) q 1 1 (C₀ s)
      (covGrad (I := I) (M := M) q 0 0 U)).toFun
  let Htop : ℝ := tensorL2Inner (I := I) (M := M) q 0 (1 + n)
    (iteratedCovGrad (I := I) q 0 1 n
      (covGrad (I := I) (M := M) q 0 0 U)).toFun
    (ccOperatorFieldComp (I := I) (M := M) q 0 (1 + n) (1 + n)
      (slotExtendIter (I := I) (M := M) q 1 1 n (C₀ s))
      (iteratedCovGrad (I := I) q 0 1 n
        (covGrad (I := I) (M := M) q 0 0 U))).toFun
  let R : ℝ := tensorL2Inner (I := I) (M := M) q 0 0
    (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
    (operatorFieldApply (I := I) (M := M) q 1 0 (Φ s)
      (covGrad (I := I) (M := M) q 0 0 U)).toFun
  let J : ℝ := (∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖) *
    (∑ j ∈ Finset.range (n + 2),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖)
  have htrans : |G₀ - Htop| ≤ Ct * J := by
    simpa only [G₀, Htop, J] using hCt s hs U
  have hder : |R| ≤ Cd * J := by
    simpa only [R, J] using hCd s hs U
  have hgrad : iteratedCovGrad (I := I) q 0 0 1 U =
      covGrad (I := I) (M := M) q 0 0 U := rfl
  have hsplit : P = -G₀ - R := by
    simpa only [P, G₀, R, C₀, Φ, hgrad,
      scalarFlux_eq_slot (I := I) (M := M)] using
      cc_pair_split (I := I) (M := M) q (G.metric ((T : ℝ) - s))
        (oneMinusConnLapSmoothIter (I := I) q 0 0 n U) U
  have hid : P + Htop = -(G₀ - Htop) - R := by
    linarith
  change |P + Htop| ≤ (Ct + Cd) * J
  rw [hid]
  calc
    |-(G₀ - Htop) - R| = |-(G₀ - Htop) + -R| := by rw [sub_eq_add_neg]
    _ ≤ |-(G₀ - Htop)| + |-R| := abs_add_le _ _
    _ = |G₀ - Htop| + |R| := by rw [abs_neg, abs_neg]
    _ ≤ Ct * J + Cd * J := add_le_add htrans hder
    _ = (Ct + Cd) * J := by ring



theorem lapCoeff_slab
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      ∃ B₂ B₁ : ℕ → ℝ,
        (∀ i, 0 ≤ B₂ i) ∧ (∀ i, 0 ≤ B₁ i) ∧
        ∀ s ∈ Set.Icc (0 : ℝ) tau,
          ((T : ℝ) - s ∈ D.regular) ∧
          (∀ i x,
            riemannianFiberNormSq (I := I) (M := M)
                (G.metric (T : ℝ)) 2 (0 + i) x
              ((iteratedCovGrad (I := I) (G.metric (T : ℝ)) 2 0 i
                (scalarTraceCoeff (I := I) (G.metric (T : ℝ))
                  (G.metric ((T : ℝ) - s)))).toSection x) ≤ B₂ i) ∧
          ∀ i x,
            riemannianFiberNormSq (I := I) (M := M)
                (G.metric (T : ℝ)) 1 (0 + i) x
              ((iteratedCovGrad (I := I) (G.metric (T : ℝ)) 1 0 i
                (connTraceCoeff (I := I) (G.metric (T : ℝ))
                  (G.metric ((T : ℝ) - s)))).toSection x) ≤ B₁ i := by
  classical
  obtain ⟨tau, htau, htau_one, J, hJ_nn, hdata⟩ :=
    metricDiff_slab (I := I) (M := M) G hG T
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let A : Set ℝ := Set.Icc (0 : ℝ) tau
  let gm : ℝ → SmoothRiemannianMetric I M := fun s => G.metric ((T : ℝ) - s)
  let P : ℝ → SmoothCcTensor q 0 2 := fun s =>
    metricDifferenceCcTensor (I := I) (M := M) q (gm s)
  have hreg : ∀ s ∈ A, (T : ℝ) - s ∈ D.regular := by
    intro s hs
    exact (hdata s hs).1
  have htie : ∀ s, s ∈ A → ∀ y v w,
      (gm s).inner y v w = q.inner y v w +
        ccTensorBilinSymm (I := I) q (P s) y v w := by
    intro s hs y v w
    simp only [P]
    rw [metricDiff_bilin (I := I) (M := M)]
    ring
  have hsmall : ∀ s, s ∈ A →
      metricCauchySchwarzBound (I := I) q
        (ccTensorBilinSymm (I := I) q (P s)) (1 / 4 : ℝ) := by
    intro s hs
    simpa only [q, P, gm] using (hdata s hs).2.1
  have hP : ∀ i s, s ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 0 (2 + i) x
        ((iteratedCovGrad (I := I) q 0 2 i (P s)).toSection x) ≤ J i := by
    intro i s hs x
    simpa only [q, P, gm] using (hdata s hs).2.2 i x
  obtain ⟨BF, hBF_nn, hBF⟩ := flux_jet_of_bdd (I := I) (M := M)
    q gm P A J hJ_nn htie hsmall hP
  obtain ⟨B₂, BT, hB₂_nn, hBT_nn, hB₂, hBT⟩ :=
    traceCast_jet_bdd (I := I) (M := M) q gm A BF hBF_nn hBF
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid
      (I := I) (M := M) q (by norm_num : (1 / 2 : ℝ) < 1)
  let BC : ℕ → ℝ := fun j => CA j *
    ∑ k ∈ Finset.range (j + 2),
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid J k
  have hBC_nn : ∀ j, 0 ≤ BC j := fun j =>
    mul_nonneg (hCA_nn j) (Finset.sum_nonneg fun k _ =>
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_nonneg J hJ_nn k)
  have hconn : ∀ j s, s ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 1 (2 + j) x
        ((iteratedCovGrad (I := I) q 1 2 j
          (connDiffSection (I := I) (gm s) q)).toSection x) ≤ BC j := by
    intro j s hs x
    have hraw := hCA (gm s) (P s) (htie s hs)
      (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (hsmall s hs) j x
    refine hraw.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCA_nn j)
    refine Finset.sum_le_sum (fun k _ => ?_)
    exact grid_mono
      (fun i => riemannianFiberNormSq_nonneg (I := I) (M := M) q 0 (2 + i) x _)
      (fun i => hP i s hs x) k
  let Tr : ℝ → SmoothCcTensor q 2 0 := fun s => traceCast (I := I) q (gm s)
  let Cd : ℝ → SmoothCcTensor q 1 2 := fun s => connDiffSection (I := I) (gm s) q
  have hTr : ∀ i s, s ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 2 (0 + i) x
        ((iteratedCovGrad (I := I) q 2 0 i (Tr s)).toSection x) ≤ BT i := by
    intro i s hs x
    simpa only [Tr] using hBT i s hs x
  have hCd : ∀ i s, s ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 1 (2 + i) x
        ((iteratedCovGrad (I := I) q 1 2 i (Cd s)).toSection x) ≤ BC i := by
    intro i s hs x
    simpa only [Cd] using hconn i s hs x
  obtain ⟨B₁, hB₁_nn, hB₁⟩ := appRS_jet_bdd (I := I) (M := M)
    q Tr Cd A BT BC hBT_nn hBC_nn hTr hCd
  let Phi : ℝ → SmoothCcTensor q 1 0 := fun s =>
    connTraceCoeff (I := I) q (gm s)
  have hPhi : ∀ i s, s ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 1 (0 + i) x
        ((iteratedCovGrad (I := I) q 1 0 i (Phi s)).toSection x) ≤ B₁ i := by
    intro i s hs x
    simpa only [Phi, Tr, Cd, connTraceCoeff] using hB₁ i s hs x
  refine ⟨tau, htau, htau_one, B₂, B₁, hB₂_nn, hB₁_nn, ?_⟩
  intro s hs
  refine ⟨hreg s hs, ?_, ?_⟩
  · intro i x
    simpa only [q, gm] using hB₂ i s hs x
  · intro i x
    simpa only [q, gm, Phi] using hPhi i s hs x



theorem cc_conn_unif
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) tau, (T : ℝ) - s ∈ D.regular) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ s ∈ Set.Icc (0 : ℝ) tau, ∀ U : SmoothCcTensor (G.metric (T : ℝ)) 0 0,
          |tensorL2Inner (I := I) (M := M) (G.metric (T : ℝ)) 0 0
              (oneMinusConnLapSmoothIter (I := I) (G.metric (T : ℝ)) 0 0 n U).toFun
              (operatorFieldApply (I := I) (M := M) (G.metric (T : ℝ)) 1 0
                (connTraceCoeff (I := I) (G.metric (T : ℝ))
                  (G.metric ((T : ℝ) - s)))
                (iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 1 U)).toFun| ≤
            C * ((∑ j ∈ Finset.range (n + 1),
                ‖iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 j U‖) *
              (∑ j ∈ Finset.range (n + 2),
                ‖iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 j U‖)) := by
  classical
  obtain ⟨tau, htau, htau_one, B₂, B₁, hB₂_nn, hB₁_nn, hcoeff⟩ :=
    lapCoeff_slab (I := I) (M := M) G hG T
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let A : Set ℝ := Set.Icc (0 : ℝ) tau
  let gm : ℝ → SmoothRiemannianMetric I M := fun s => G.metric ((T : ℝ) - s)
  have hreg : ∀ s ∈ A, (T : ℝ) - s ∈ D.regular := by
    intro s hs
    exact (hcoeff s hs).1
  let Phi : ℝ → SmoothCcTensor q 1 0 := fun s =>
    connTraceCoeff (I := I) q (gm s)
  have hPhi : ∀ i s, s ∈ A → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) q 1 (0 + i) x
        ((iteratedCovGrad (I := I) q 1 0 i (Phi s)).toSection x) ≤ B₁ i := by
    intro i s hs x
    simpa only [q, gm, Phi] using (hcoeff s hs).2.2 i x
  obtain ⟨CG, hCG_nn, hCG⟩ :=
    app_jet_of_bdd (I := I) (M := M) q 1 0 Phi A B₁ hB₁_nn hPhi
  refine ⟨tau, htau, htau_one, ?_, fun n => ?_⟩
  · intro s hs
    exact hreg s hs
  · obtain ⟨C, hC_nn, hC⟩ :=
      iterL_pair_jet_of (I := I) (M := M) q 0 n Phi A CG hCG_nn hCG
    refine ⟨C, hC_nn, ?_⟩
    intro s hs U
    simpa only [q, A, Phi, gm] using hC s hs U




theorem cc_lap_unif
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) tau, (T : ℝ) - s ∈ D.regular) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ s ∈ Set.Icc (0 : ℝ) tau, ∀ U : SmoothCcTensor (G.metric (T : ℝ)) 0 0,
          tensorL2Inner (I := I) (M := M) (G.metric (T : ℝ)) 0 0
              (oneMinusConnLapSmoothIter (I := I) (G.metric (T : ℝ)) 0 0 n U).toFun
              (scalarLapDiffCc (I := I) (G.metric (T : ℝ))
                (G.metric ((T : ℝ) - s)) U).toFun ≤
            ((1 : ℝ) / 3) *
                ‖SmoothCcTensor.toL2
                  (castCcTensorRank (I := I) (M := M) (G.metric (T : ℝ)) 0
                    (by omega : 0 + (n + 1) = 1 + n)
                    (iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 (n + 1) U))‖ ^ 2 +
              C * ((∑ j ∈ Finset.range (n + 1),
                  ‖iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 j U‖) *
                (∑ j ∈ Finset.range (n + 2),
                  ‖iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 0 j U‖)) := by
  classical
  obtain ⟨taup, htaup, htaup_one, hp⟩ := cc_comm_unif (I := I) (M := M) G hG T
  obtain ⟨tauc, htauc, _, _, hc⟩ :=
    cc_conn_unif (I := I) (M := M) G hG T
  obtain ⟨taum, htaum, _, _, _, hm⟩ :=
    metricDiff_slab (I := I) (M := M) G hG T
  let tau : ℝ := min taup (min tauc taum)
  have htau : 0 < tau := by
    exact lt_min htaup (lt_min htauc htaum)
  have htau_one : tau ≤ 1 := by
    exact (min_le_left taup (min tauc taum)).trans htaup_one
  have htaup_le : tau ≤ taup := min_le_left _ _
  have htauc_le : tau ≤ tauc :=
    (min_le_right taup (min tauc taum)).trans (min_le_left tauc taum)
  have htaum_le : tau ≤ taum :=
    (min_le_right taup (min tauc taum)).trans (min_le_right tauc taum)
  have hreg : ∀ s ∈ Set.Icc (0 : ℝ) tau, (T : ℝ) - s ∈ D.regular := by
    intro s hs
    exact (hm s ⟨hs.1, hs.2.trans htaum_le⟩).1
  refine ⟨tau, htau, htau_one, hreg, fun n => ?_⟩
  obtain ⟨Cp, hCp_nn, hCp⟩ := hp n
  obtain ⟨Cc, hCc_nn, hCc⟩ := hc n
  refine ⟨Cp + Cc, add_nonneg hCp_nn hCc_nn, ?_⟩
  intro s hs U
  have hsp : s ∈ Set.Icc (0 : ℝ) taup := ⟨hs.1, hs.2.trans htaup_le⟩
  have hsc : s ∈ Set.Icc (0 : ℝ) tauc := ⟨hs.1, hs.2.trans htauc_le⟩
  have hsm : s ∈ Set.Icc (0 : ℝ) taum := ⟨hs.1, hs.2.trans htaum_le⟩
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let h : SmoothRiemannianMetric I M := G.metric ((T : ℝ) - s)
  let K : SmoothCcTensor q 0 2 :=
    metricDifferenceCcTensor (I := I) (M := M) q h
  let k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    ccTensorBilinSymm (I := I) q K
  have htie : ∀ y v w, h.inner y v w = q.inner y v w + k y v w := by
    intro y v w
    simp only [k, K]
    rw [metricDiff_bilin (I := I) (M := M)]
    ring
  have hsmall : metricCauchySchwarzBound (I := I) q k (1 / 4 : ℝ) := by
    simpa only [q, h, K, k] using (hm s hsm).2.1
  let X : SmoothCcTensor q 0 0 :=
    oneMinusConnLapSmoothIter (I := I) q 0 0 n U
  let A : SmoothCcTensor q 0 0 :=
    operatorFieldApply (I := I) (M := M) q 2 0 (scalarTraceCoeff (I := I) q h)
      (iteratedCovGrad (I := I) q 0 0 2 U)
  let B : SmoothCcTensor q 0 0 :=
    operatorFieldApply (I := I) (M := M) q 1 0 (connTraceCoeff (I := I) q h)
      (iteratedCovGrad (I := I) q 0 0 1 U)
  let Atop : SmoothCcTensor q 0 (1 + n) :=
    castCcTensorRank (I := I) (M := M) q 0
      (by omega : 0 + (n + 1) = 1 + n)
      (iteratedCovGrad (I := I) q 0 0 (n + 1) U)
  let P : ℝ := tensorL2Inner (I := I) (M := M) q 0 0 X.toFun A.toFun
  let Q : ℝ := tensorL2Inner (I := I) (M := M) q 0 0 X.toFun B.toFun
  let Htop : ℝ := tensorL2Inner (I := I) (M := M) q 0 (1 + n) Atop.toFun
    (ccOperatorFieldComp (I := I) (M := M) q 0 (1 + n) (1 + n)
      (slotExtendIter (I := I) (M := M) q 1 1 n
        (scalarFluxCoeff (I := I) q h)) Atop).toFun
  let Dtop : ℝ := ((1 : ℝ) / 3) * ‖SmoothCcTensor.toL2 Atop‖ ^ 2
  let J : ℝ := (∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖) *
    (∑ j ∈ Finset.range (n + 2),
      ‖iteratedCovGrad (I := I) q 0 0 j U‖)
  have hfront :
      iteratedCovGrad (I := I) q 0 1 n
          (covGrad (I := I) (M := M) q 0 0 U) = Atop := by
    dsimp only [Atop]
    apply eq_of_heq
    exact HEq.trans
      (iteratedCovGrad_covGrad_comm_heq' (I := I) (M := M) q 0 0 n U)
      (castRankCc_db_heq (I := I) (M := M) q 0
        (by omega : 0 + (n + 1) = 1 + n)
        (iteratedCovGrad (I := I) q 0 0 (n + 1) U)).symm
  have hcomm : |P + Htop| ≤ Cp * J := by
    have hcomm' := hCp s hsp U
    rw [hfront] at hcomm'
    simpa only [q, h, X, A, P, Htop, J] using hcomm'
  have hlast : -Htop ≤ Dtop := by
    have hlast' := cc_last_pair (I := I) (M := M) q h k htie
      (by norm_num : (1 / 4 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 1 / 4)
      hsmall n U
    rw [show ((1 / 4 : ℝ) / (1 - 1 / 4)) = 1 / 3 by norm_num] at hlast'
    simpa only [Htop, Atop, Dtop, scalarFlux_eq_slot (I := I) (M := M)] using hlast'
  have hprincipal : P ≤ Dtop + Cp * J := by
    have hsum : P + Htop ≤ Cp * J :=
      le_trans (le_abs_self (P + Htop)) hcomm
    linarith
  have hconnection : -Q ≤ Cc * J := by
    exact le_trans (neg_le_abs Q)
      (by simpa only [q, h, X, B, Q, J] using hCc s hsc U)
  have hsplit :
      tensorL2Inner (I := I) (M := M) q 0 0 X.toFun
          (scalarLapDiffCc (I := I) q h U).toFun = P - Q := by
    rw [scalarLapDiffCc]
    calc
      tensorL2Inner (I := I) (M := M) q 0 0 X.toFun (A - B).toFun =
          (⟪X, A - B⟫_ℝ : ℝ) :=
        (SmoothCcTensor.inner_def (I := I) (M := M) X (A - B)).symm
      _ = (⟪X, A⟫_ℝ : ℝ) - (⟪X, B⟫_ℝ : ℝ) := by rw [inner_sub_right]
      _ = P - Q := by
        rw [SmoothCcTensor.inner_def, SmoothCcTensor.inner_def]
  rw [show
    tensorL2Inner (I := I) (M := M) q 0 0
        (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
        (scalarLapDiffCc (I := I) q h U).toFun = P - Q by
      simpa only [X] using hsplit]
  change P - Q ≤ Dtop + (Cp + Cc) * J
  rw [sub_eq_add_neg]
  calc
    P + -Q ≤ (Dtop + Cp * J) + Cc * J := add_le_add hprincipal hconnection
    _ = Dtop + (Cp + Cc) * J := by ring

private theorem finite_lap_unif
    (q : SmoothRiemannianMetric I M) {alpha : Type*}
    (h : alpha → SmoothRiemannianMetric I M) (A : Set alpha)
    (n : ℕ) (Clap : ℝ) (hClap_nn : 0 ≤ Clap)
    (hlap : ∀ t, t ∈ A → ∀ U : SmoothCcTensor q 0 0,
      tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
          (scalarLapDiffCc (I := I) q (h t) U).toFun ≤
        ((1 : ℝ) / 3) *
            ‖SmoothCcTensor.toL2
              (castCcTensorRank (I := I) (M := M) q 0
                (by omega : 0 + (n + 1) = 1 + n)
                (iteratedCovGrad (I := I) q 0 0 (n + 1) U))‖ ^ 2 +
          Clap * ((∑ j ∈ Finset.range (n + 1),
              ‖iteratedCovGrad (I := I) q 0 0 j U‖) *
            (∑ j ∈ Finset.range (n + 2),
              ‖iteratedCovGrad (I := I) q 0 0 j U‖))) :
    ∃ Cmid : ℝ, 0 ≤ Cmid ∧
      ∀ t, t ∈ A → ∀ (v : tensorHs (I := I) (M := M) q 0 0 0)
        (hv : (Function.support v.coeff).Finite),
        2 * ∑ i ∈ hv.toFinset,
            tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
              (v.coeff i *
                tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
                  (SmoothCcTensor.toL2
                    (scalarLapDiffCc (I := I) q (h t)
                      (tensorHsSmoothRepr (I := I) (M := M) v hv))) i) ≤
          ((5 : ℝ) / 3) *
              (∑ i ∈ hv.toFinset,
                tensorSobolevWeight (I := I) (M := M) i ((n + 1 : ℕ) : ℝ) *
                  (v.coeff i) ^ 2) +
            Cmid *
              (∑ i ∈ hv.toFinset,
                tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
                  (v.coeff i) ^ 2) := by
  classical
  obtain ⟨Cgap, hCgap_nn, hgap⟩ := cc_dirichlet_gap (I := I) (M := M) q 0 n
  obtain ⟨Clo, hClo_nn, hlo⟩ := hsJet_le (I := I) (M := M) q 0 n
  obtain ⟨Chi, hChi_nn, hhi⟩ := hsJet_le (I := I) (M := M) q 0 (n + 1)
  let Pcoef : ℝ := Clap * Clo * Chi
  refine ⟨((2 : ℝ) / 3) * Cgap + Pcoef ^ 2, by positivity, ?_⟩
  intro t ht v hv
  let U : SmoothCcTensor q 0 0 :=
    tensorHsSmoothRepr (I := I) (M := M) v hv
  let L : SmoothCcTensor q 0 0 := scalarLapDiffCc (I := I) q (h t) U
  let Jlo : ℝ :=
    ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) q 0 0 j U‖
  let Jhi : ℝ :=
    ∑ j ∈ Finset.range (n + 2), ‖iteratedCovGrad (I := I) q 0 0 j U‖
  let Hlo : ℝ := ‖ccTensorToHs (I := I) (M := M) q 0 (n : ℝ) U‖
  let Hhi : ℝ := ‖ccTensorToHs (I := I) (M := M) q 0 ((n + 1 : ℕ) : ℝ) U‖
  have hcastNorm :
      ‖SmoothCcTensor.toL2
          (castCcTensorRank (I := I) (M := M) q 0
            (by omega : 0 + (n + 1) = 1 + n)
            (iteratedCovGrad (I := I) q 0 0 (n + 1) U))‖ =
        ‖SmoothCcTensor.toL2
          (iteratedCovGrad (I := I) q 0 0 (n + 1) U)‖ := by
    rw [SmoothCcTensor.norm_toL2, SmoothCcTensor.norm_toL2,
      DiffBilinOp.norm_castCcTensorRank]
  have hlapU :
      tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun L.toFun ≤
        ((1 : ℝ) / 3) *
            ‖SmoothCcTensor.toL2
              (iteratedCovGrad (I := I) q 0 0 (n + 1) U)‖ ^ 2 +
          Clap * (Jlo * Jhi) := by
    have hmain := hlap t ht U
    rw [hcastNorm] at hmain
    simpa only [L, Jlo, Jhi] using hmain
  have hgapU :
      ‖SmoothCcTensor.toL2
          (iteratedCovGrad (I := I) q 0 0 (n + 1) U)‖ ^ 2 ≤
        Hhi ^ 2 + Cgap * Hlo ^ 2 := by
    have hn : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
    dsimp only [Hhi, Hlo]
    rw [hn]
    exact hgap U
  have hloU : Jlo ≤ Clo * Hlo := by
    simpa only [Jlo, Hlo] using hlo U
  have hhiU : Jhi ≤ Chi * Hhi := by
    have hmain := hhi U
    simpa only [Jhi, Hhi, show n + 1 + 1 = n + 2 by omega] using hmain
  have hJlo_nn : 0 ≤ Jlo := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hJhi_nn : 0 ≤ Jhi := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hHlo_nn : 0 ≤ Hlo := norm_nonneg _
  have hprod : Jlo * Jhi ≤ (Clo * Hlo) * (Chi * Hhi) :=
    mul_le_mul hloU hhiU hJhi_nn (mul_nonneg hClo_nn hHlo_nn)
  have hrem : Clap * (Jlo * Jhi) ≤ Pcoef * Hlo * Hhi := by
    calc
      Clap * (Jlo * Jhi) ≤ Clap * ((Clo * Hlo) * (Chi * Hhi)) :=
        mul_le_mul_of_nonneg_left hprod hClap_nn
      _ = Pcoef * Hlo * Hhi := by simp only [Pcoef]; ring
  have hyoung :
      2 * (Clap * (Jlo * Jhi)) ≤ Hhi ^ 2 + Pcoef ^ 2 * Hlo ^ 2 := by
    have hsquare : 0 ≤ (Hhi - Pcoef * Hlo) ^ 2 := sq_nonneg _
    nlinarith [hrem]
  have hmain :
      2 * tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun L.toFun ≤
        ((5 : ℝ) / 3) * Hhi ^ 2 +
          (((2 : ℝ) / 3) * Cgap + Pcoef ^ 2) * Hlo ^ 2 := by
    nlinarith [hlapU, hgapU, hyoung]
  let hc := tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0
  have hrepr (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) q 0 0) :
      tensorL2Coeff (I := I) (M := M) hc (SmoothCcTensor.toL2 U) i = v.coeff i := by
    dsimp only [U]
    rw [SmoothCcTensor.toL2_apply,
      tensorHsSmoothRepr_toL2 (I := I) (M := M) (le_refl (0 : ℝ)) v hv,
      tensorHsToL2_tensorL2Coeff (I := I) (M := M) (le_refl (0 : ℝ))]
  have hhs (m : ℕ) :
      ccTensorToHs (I := I) (M := M) q 0 (m : ℝ) U =
        tensorHsOfFiniteSupport (I := I) (M := M) (m : ℝ) v.coeff hv := by
    apply tensorHs.ext
    funext i
    rw [ccTensorToHs_coeff, tensorHsOfFiniteSupport_coeff]
    exact hrepr i
  have henergy (m : ℕ) :
      ‖tensorHsOfFiniteSupport (I := I) (M := M) (m : ℝ) v.coeff hv‖ ^ 2 =
        ∑ i ∈ hv.toFinset,
          tensorSobolevWeight (I := I) (M := M) i (m : ℝ) * (v.coeff i) ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum]
    simp only [tensorHsOfFiniteSupport_coeff]
    rw [tsum_eq_sum (s := hv.toFinset)]
    intro i hi
    have hcoeff : v.coeff i = 0 := by
      by_contra hne
      exact hi (hv.mem_toFinset.mpr (Function.mem_support.mpr hne))
    norm_num [hcoeff]
  have hmain' :
      2 * tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun L.toFun ≤
        ((5 : ℝ) / 3) *
            (∑ i ∈ hv.toFinset,
              tensorSobolevWeight (I := I) (M := M) i ((n + 1 : ℕ) : ℝ) *
                (v.coeff i) ^ 2) +
          (((2 : ℝ) / 3) * Cgap + Pcoef ^ 2) *
            (∑ i ∈ hv.toFinset,
              tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
                (v.coeff i) ^ 2) := by
    dsimp only [Hhi, Hlo] at hmain
    rw [hhs (n + 1), hhs n, henergy (n + 1), henergy n] at hmain
    exact hmain
  have hpair := finite_cc_pair (I := I) (M := M) q 0 n v hv L
  rw [hpair]
  simpa only [U, L] using hmain'



theorem cc_a2_unif
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) tau, (T : ℝ) - s ∈ D.regular) ∧
      ∀ n : ℕ, ∃ Cmid : ℝ, 0 ≤ Cmid ∧
        ∀ s ∈ Set.Icc (0 : ℝ) tau,
          ∀ (F : Finset
              (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) (G.metric (T : ℝ)) 0 0))
            (v : tensorHs (I := I) (M := M) (G.metric (T : ℝ)) 0 0 0)
            (hv : (Function.support v.coeff).Finite),
            hv.toFinset ⊆ F →
              2 * ∑ i ∈ F,
                  tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
                    (v.coeff i *
                      tensorL2Coeff (I := I) (M := M)
                        (tensorResolventL2_isCompactOperator
                          (I := I) (M := M) (G.metric (T : ℝ)) 0 0)
                        (SmoothCcTensor.toL2
                          (scalarLapDiffCc (I := I) (G.metric (T : ℝ))
                            (G.metric ((T : ℝ) - s))
                            (tensorHsSmoothRepr (I := I) (M := M) v hv))) i) ≤
                ((5 : ℝ) / 3) *
                    (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i
                          ((n + 1 : ℕ) : ℝ) * (v.coeff i) ^ 2) +
                  Cmid *
                    (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
                        (v.coeff i) ^ 2) := by
  classical
  obtain ⟨tau, htau, htau_one, hreg, hlap⟩ :=
    cc_lap_unif (I := I) (M := M) G hG T
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let gm : ℝ → SmoothRiemannianMetric I M := fun s => G.metric ((T : ℝ) - s)
  let A : Set ℝ := Set.Icc (0 : ℝ) tau
  refine ⟨tau, htau, htau_one, hreg, fun n => ?_⟩
  obtain ⟨Clap, hClap_nn, hClap⟩ := hlap n
  have hlap' : ∀ s, s ∈ A → ∀ U : SmoothCcTensor q 0 0,
      tensorL2Inner (I := I) (M := M) q 0 0
          (oneMinusConnLapSmoothIter (I := I) q 0 0 n U).toFun
          (scalarLapDiffCc (I := I) q (gm s) U).toFun ≤
        ((1 : ℝ) / 3) *
            ‖SmoothCcTensor.toL2
              (castCcTensorRank (I := I) (M := M) q 0
                (by omega : 0 + (n + 1) = 1 + n)
                (iteratedCovGrad (I := I) q 0 0 (n + 1) U))‖ ^ 2 +
          Clap * ((∑ j ∈ Finset.range (n + 1),
              ‖iteratedCovGrad (I := I) q 0 0 j U‖) *
            (∑ j ∈ Finset.range (n + 2),
              ‖iteratedCovGrad (I := I) q 0 0 j U‖)) := by
    intro s hs U
    simpa only [q, gm, A] using hClap s hs U
  obtain ⟨Cmid, hCmid_nn, hcore⟩ :=
    finite_lap_unif (I := I) (M := M) q gm A n Clap hClap_nn hlap'
  refine ⟨Cmid, hCmid_nn, ?_⟩
  intro s hs F v hv hsub
  have hcoeff {i} (hi : i ∉ hv.toFinset) : v.coeff i = 0 := by
    by_contra hne
    exact hi (hv.mem_toFinset.mpr (Function.mem_support.mpr hne))
  have hlhs :
      (∑ i ∈ hv.toFinset,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (v.coeff i * tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator
                (I := I) (M := M) q 0 0)
              (SmoothCcTensor.toL2
                (scalarLapDiffCc (I := I) q (gm s)
                  (tensorHsSmoothRepr (I := I) (M := M) v hv))) i)) =
        ∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (v.coeff i * tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator
                (I := I) (M := M) q 0 0)
              (SmoothCcTensor.toL2
                (scalarLapDiffCc (I := I) q (gm s)
                  (tensorHsSmoothRepr (I := I) (M := M) v hv))) i) := by
    apply Finset.sum_subset hsub
    intro i hi hiF
    rw [hcoeff hiF, zero_mul, mul_zero]
  have hhi :
      (∑ i ∈ hv.toFinset,
          tensorSobolevWeight (I := I) (M := M) i ((n + 1 : ℕ) : ℝ) *
            (v.coeff i) ^ 2) =
        ∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i ((n + 1 : ℕ) : ℝ) *
            (v.coeff i) ^ 2 := by
    apply Finset.sum_subset hsub
    intro i hi hiF
    norm_num [hcoeff hiF]
  have hlo :
      (∑ i ∈ hv.toFinset,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (v.coeff i) ^ 2) =
        ∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (n : ℝ) *
            (v.coeff i) ^ 2 := by
    apply Finset.sum_subset hsub
    intro i hi hiF
    norm_num [hcoeff hiF]
  have hmain := hcore s (by simpa only [A] using hs) v hv
  rw [hlhs, hhi, hlo] at hmain
  simpa only [q, gm, A] using hmain

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
