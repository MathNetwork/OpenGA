import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamChartRicciDeriv
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamLinearizedChristoffel
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciSecondOrderPart
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffUniformBounds
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldTameEnvelope
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.SecondCovGradChartHessian
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SmoothParametricCoeffIntegral
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Geometry.Flow.DeTurckVFChartCoord
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCm
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamCurvatureJetBound
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RealizeMetricChartGramDifference


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory intervalIntegral
open scoped Manifold Topology ContDiff BigOperators Matrix Interval

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_smul_value_appCc
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (c : ℝ)
    (v : Tensor0SBundle.TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma gFibreOpBound_mono_local
    (g₀ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    {δ δ' : ℝ} (hle : δ ≤ δ') (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ) :
    metricCauchySchwarzBound (I := I) (M := M) g₀ h δ' := by
  intro x v w
  refine le_trans (hδ x v w) ?_
  have hsv : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hsw : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hprod : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg hsv hsw
  nlinarith [hle, hprod]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem exists_orthoFrame_basis_local (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
      (bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x)),
      (∀ i : Fin (Module.finrank ℝ E), bse i = e i) ∧
      (∀ a b : Fin (Module.finrank ℝ E),
        g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) := by
  classical
  obtain ⟨n, e0, hn, horth0, _hpars, _hrepr⟩ :=
    DifferentialGeometry.Integral.Connection.exists_orthonormal_frame_riemannianFiberNormSq
      (I := I) (M := M) g 0 0 x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  subst hnE
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x := e0 with he_def
  have horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := horth0
  haveI : Nonempty (Fin (Module.finrank ℝ (TangentSpace I x))) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hcard : Fintype.card (Fin (Module.finrank ℝ (TangentSpace I x))) =
      Module.finrank ℝ (TangentSpace I x) := Fintype.card_fin _
  refine ⟨e, basisOfLinearIndependentOfCardEqFinrank he_li hcard, fun i => ?_, horth⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem riemannianFiberNormSq_le_of_orthonormalFrame_componentSumSq_le
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (S : TensorRSSpace r s I x)
    (C : ℝ)
    (hKsum : ∀ (e : Fin (Module.finrank ℝ E) → TangentSpace I x),
      (∀ a b : Fin (Module.finrank ℝ E),
        g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) →
      ∀ (K : Fin r → Fin (Module.finrank ℝ E)),
        (∑ J : Fin s → Fin (Module.finrank ℝ E),
          (fiberNormSqComponent (I := I) (M := M) g₀ x r s S (Module.finrank ℝ E) e K J) ^ 2)
          ≤ C ^ 2) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x S
      ≤ ((Module.finrank ℝ E : ℝ) ^ r) * C ^ 2 := by
  classical
  obtain ⟨e, bse, hbse, horth⟩ := exists_orthoFrame_basis_local (I := I) (M := M) g₀ x
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ r s x S e bse rfl hbse horth]
  calc (∑ K : Fin r → Fin (Module.finrank ℝ E), ∑ J : Fin s → Fin (Module.finrank ℝ E),
          (fiberNormSqComponent (I := I) (M := M) g₀ x r s S (Module.finrank ℝ E) e K J) ^ 2)
      ≤ ∑ _K : Fin r → Fin (Module.finrank ℝ E), C ^ 2 :=
        Finset.sum_le_sum (fun K _ => hKsum e horth K)
    _ = ((Module.finrank ℝ E : ℝ) ^ r) * C ^ 2 := by
        rw [Finset.sum_const]
        simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_pow]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metricInner_injective_local (g₁ : SmoothRiemannianMetric I M) (x : M)
    {a b : TangentSpace I x}
    (hab : ∀ w : TangentSpace I x, g₁.inner x a w = g₁.inner x b w) : a = b := by
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g₁.pos x (a - b) hsub
  have hzero : g₁.inner x (a - b) (a - b) = 0 := by
    have hsymm₁ : g₁.inner x (a - b) (a - b) =
        g₁.inner x (a - b) a - g₁.inner x (a - b) b := by rw [← map_sub]
    rw [hsymm₁, g₁.symm x (a - b) a, g₁.symm x (a - b) b]
    have e1 : g₁.inner x a (a - b) = g₁.inner x b (a - b) := hab (a - b)
    rw [e1]; ring
  exact absurd hzero (ne_of_gt hpos)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cometric_sum_eq_invSharp (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (b : TangentSpace I x) :
    ∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x b ((Module.finBasis ℝ E) k) •
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) =
      inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x b) := by
  classical
  apply metricInner_injective_local (I := I) g₁ x
  intro w
  have hcoord : ∀ k : Fin (Module.finrank ℝ E),
      (Module.finBasis ℝ E).cDualBasis k (w : E) =
        (Module.finBasis ℝ E).repr (w : E) k := by
    intro k
    rw [show ((Module.finBasis ℝ E).cDualBasis k) =
        LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) from by
      rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
      congr 1
      exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k]
    rw [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  rw [map_sum, ContinuousLinearMap.sum_apply]
  have hlhs : ∀ k : Fin (Module.finrank ℝ E),
      (g₁.inner x (g₀.inner x b ((Module.finBasis ℝ E) k) •
          cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))) w =
        g₀.inner x b ((Module.finBasis ℝ E) k) *
          (Module.finBasis ℝ E).repr (w : E) k := by
    intro k
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    congr 1
    have hinner : g₁.inner x (cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) w =
        (Module.finBasis ℝ E).cDualBasis k (w : E) := by
      have h1 : cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) =
          inverseMetricSharpFib (I := I) g₁ x
            ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 x).symm
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) := rfl
      rw [h1, inverseMetricSharpFib_inner (I := I) g₁ x _ w, cotangentToDualLinear_apply,
        cotangentToDual_apply]
      change (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) (fun _ : Fin 1 => (w : E)) = _
      rw [Tensor0SBundle.model_covectorOfCLM_apply]
    rw [hinner, hcoord k]
  rw [Finset.sum_congr rfl (fun k _ => hlhs k)]
  rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_g0FlatCLM]
  have hwexp : (w : TangentSpace I x) =
      ∑ k : Fin (Module.finrank ℝ E),
        (Module.finBasis ℝ E).repr (w : E) k • ((Module.finBasis ℝ E) k : TangentSpace I x) := by
    have h := (Module.finBasis ℝ E).sum_repr (w : E)
    exact h.symm
  conv_rhs => rw [hwexp, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ContinuousLinearMap.map_smul, smul_eq_mul, mul_comm]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma abs_g0_inner_invSharp_le (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ) (x : M)
    (a b : TangentSpace I x)
    (hua : g₀.inner x a a ≤ 1) (hub : g₀.inner x b b ≤ 1) :
    |g₀.inner x a (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x b))| ≤
      1 / (1 - δ) := by
  set f : TangentSpace I x :=
    inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x b) with hf
  have hcs := DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
    (I := I) (M := M) g₀ x a f
  have hfbound := norm_inverseMetricSharpFib_g0Flat_le (I := I) g₀ g₁ h htie
    hδ_lt hδ_nn hδ x b
  rw [← hf] at hfbound
  have hsa_nn : 0 ≤ Real.sqrt (g₀.inner x a a) := Real.sqrt_nonneg _
  have hsb_le : Real.sqrt (g₀.inner x b b) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hub
  have hsa_le : Real.sqrt (g₀.inner x a a) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hua
  have hcoeff : 0 < 1 - δ := by linarith
  have hinv_nn : 0 ≤ 1 / (1 - δ) := by positivity
  have hsf_nn : 0 ≤ Real.sqrt (g₀.inner x f f) := Real.sqrt_nonneg _
  calc |g₀.inner x a f|
      ≤ Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x f f) := hcs
    _ ≤ Real.sqrt (g₀.inner x a a) * ((1 / (1 - δ)) * Real.sqrt (g₀.inner x b b)) :=
        mul_le_mul_of_nonneg_left hfbound hsa_nn
    _ ≤ 1 * ((1 / (1 - δ)) * 1) := by
        apply mul_le_mul hsa_le _ (by positivity) (by norm_num)
        exact mul_le_mul_of_nonneg_left hsb_le hinv_nn
    _ = 1 / (1 - δ) := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cometric_dualsum_inner_collapse (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (a c : TangentSpace I x) :
    (∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x c ((Module.finBasis ℝ E) k) *
          g₀.inner x a (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))) =
      g₀.inner x a (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x c)) := by
  classical
  have hsumeq := cometric_sum_eq_invSharp (I := I) g₀ g₁ x c
  calc (∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x c ((Module.finBasis ℝ E) k) *
          g₀.inner x a (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))))
      = ∑ k : Fin (Module.finrank ℝ E), g₀.inner x a
          (g₀.inner x c ((Module.finBasis ℝ E) k) •
            cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    _ = g₀.inner x a
          (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x c ((Module.finBasis ℝ E) k) •
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) := (map_sum (g₀.inner x a) _ _).symm
    _ = g₀.inner x a (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x c)) := by
        rw [hsumeq]

private lemma ricciArm_compSq_le_indicator {A C R : ℝ} (hAbound : |A| ≤ R) (hCbound : |C| ≤ R)
    {nn : ℕ} (K : Fin 4 → Fin nn) (J : Fin 2 → Fin nn) :
    ((1 / 2 : ℝ) *
        (A * ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0))
          + A * ((if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0))
          - C * ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)))) ^ 2
      ≤ (3 / 4 : ℝ) * R ^ 2 *
          ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0)
            + (if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0)
            + (if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
  classical
  set χa : ℝ := (if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0) with hχa
  set χb : ℝ := (if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0) with hχb
  set χc : ℝ := (if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0) with hχc
  have hχa01 : χa = 0 ∨ χa = 1 := by
    rw [hχa]; by_cases h1 : K 1 = J 0 <;> by_cases h2 : K 2 = J 1 <;> simp [h1, h2]
  have hχb01 : χb = 0 ∨ χb = 1 := by
    rw [hχb]; by_cases h1 : K 1 = J 1 <;> by_cases h2 : K 2 = J 0 <;> simp [h1, h2]
  have hχc01 : χc = 0 ∨ χc = 1 := by
    rw [hχc]; by_cases h1 : K 2 = J 0 <;> by_cases h2 : K 3 = J 1 <;> simp [h1, h2]
  have hA2 : A ^ 2 ≤ R ^ 2 := by
    have := sq_abs A; nlinarith [hAbound, abs_nonneg A]
  have hC2 : C ^ 2 ≤ R ^ 2 := by
    have := sq_abs C; nlinarith [hCbound, abs_nonneg C]
  have hR2nn : 0 ≤ R ^ 2 := sq_nonneg R
  rcases hχa01 with ha | ha <;> rcases hχb01 with hb | hb <;> rcases hχc01 with hc | hc <;>
    rw [ha, hb, hc] <;> nlinarith [hA2, hC2, hR2nn, sq_nonneg (A - C),
      sq_nonneg (A + A), sq_nonneg (A + A - C), sq_nonneg A, sq_nonneg C]

private lemma ricciArm_indicatorSum_le {nn : ℕ} (K : Fin 4 → Fin nn) (R : ℝ) :
    (∑ J : Fin 2 → Fin nn,
        (3 / 4 : ℝ) * R ^ 2 *
          ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0)
            + (if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0)
            + (if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)))
      ≤ (9 / 4 : ℝ) * R ^ 2 := by
  classical
  have hpair : ∀ (a b : Fin nn),
      (∑ J : Fin 2 → Fin nn,
        (if a = J 0 then (1 : ℝ) else 0) * (if b = J 1 then (1 : ℝ) else 0)) = 1 := by
    intro a b
    rw [← (finTwoArrowEquiv (Fin nn)).symm.sum_comp
      (fun J : Fin 2 → Fin nn =>
        (if a = J 0 then (1 : ℝ) else 0) * (if b = J 1 then (1 : ℝ) else 0))]
    rw [Fintype.sum_prod_type]
    simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hin : ∀ j0 : Fin nn,
        (∑ j1 : Fin nn, (if a = j0 then (1 : ℝ) else 0) * (if b = j1 then (1 : ℝ) else 0))
          = (if a = j0 then (1 : ℝ) else 0) := by
      intro j0
      rw [← Finset.mul_sum, Finset.sum_ite_eq Finset.univ b (fun _ => (1 : ℝ))]
      simp
    rw [Finset.sum_congr rfl (fun j0 _ => hin j0)]
    rw [Finset.sum_ite_eq Finset.univ a (fun _ => (1 : ℝ))]; simp
  have hpairSwap : ∀ (a b : Fin nn),
      (∑ J : Fin 2 → Fin nn,
        (if a = J 1 then (1 : ℝ) else 0) * (if b = J 0 then (1 : ℝ) else 0)) = 1 := by
    intro a b
    rw [← (finTwoArrowEquiv (Fin nn)).symm.sum_comp
      (fun J : Fin 2 → Fin nn =>
        (if a = J 1 then (1 : ℝ) else 0) * (if b = J 0 then (1 : ℝ) else 0))]
    rw [Fintype.sum_prod_type]
    simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hin : ∀ j0 : Fin nn,
        (∑ j1 : Fin nn, (if a = j1 then (1 : ℝ) else 0) * (if b = j0 then (1 : ℝ) else 0))
          = (if b = j0 then (1 : ℝ) else 0) := by
      intro j0
      rw [← Finset.sum_mul, Finset.sum_ite_eq Finset.univ a (fun _ => (1 : ℝ))]; simp
    rw [Finset.sum_congr rfl (fun j0 _ => hin j0)]
    rw [Finset.sum_ite_eq Finset.univ b (fun _ => (1 : ℝ))]; simp
  rw [← Finset.mul_sum]
  have hsum3 : (∑ J : Fin 2 → Fin nn,
        ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0)
          + (if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0)
          + (if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) = 3 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [hpair (K 1) (K 2), hpairSwap (K 1) (K 2), hpair (K 2) (K 3)]; norm_num
  rw [hsum3]
  have hfinal : (9 / 4 : ℝ) * R ^ 2 = (3 / 4 : ℝ) * R ^ 2 * 3 := by ring
  rw [hfinal]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma ricciArm_dim1_compSq_le {A C R : ℝ} (hAbound : |A| ≤ R)
    (hAeqC : A = C)
    (hfr : Module.finrank ℝ E = 1) (K : Fin 4 → Fin (Module.finrank ℝ E)) :
    (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) *
          (A * ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0))
            + A * ((if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0))
            - C * ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)))) ^ 2)
      ≤ R ^ 2 := by
  classical
  have hAR : 0 ≤ R := le_trans (abs_nonneg A) hAbound
  have hsub : Subsingleton (Fin (Module.finrank ℝ E)) := by
    rw [hfr]; infer_instance
  have hKJ : ∀ (a b : Fin (Module.finrank ℝ E)), (if a = b then (1 : ℝ) else 0) = 1 := by
    intro a b; rw [if_pos (Subsingleton.elim a b)]
  have hcard : Fintype.card (Fin 2 → Fin (Module.finrank ℝ E)) = 1 := by
    rw [Fintype.card_fun, Fintype.card_fin, hfr]; norm_num
  have hACeq : (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) *
          (A * ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0))
            + A * ((if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0))
            - C * ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)))) ^ 2)
      = ∑ _J : Fin 2 → Fin (Module.finrank ℝ E), ((1 / 2 : ℝ) * A) ^ 2 := by
    refine Finset.sum_congr rfl (fun J _ => ?_)
    simp only [hKJ]
    rw [← hAeqC]
    ring_nf
  rw [hACeq, Finset.sum_const]
  simp only [Finset.card_univ, hcard, one_smul]
  have hA2 : A ^ 2 ≤ R ^ 2 := by
    have := sq_abs A; nlinarith [hAbound, abs_nonneg A]
  nlinarith [hA2, sq_nonneg A]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem ricciArmPrincipalCoeffFib_fiberComponent_Ksum_sq_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 4 → Fin (Module.finrank ℝ E)) :
    (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          TensorRSSpace.ofCLM (ricciDeTurckPrincipalCoeffAtPoint (I := I) g₁ x))
        (Module.finrank ℝ E) e K J) ^ 2)
      ≤ ((Module.finrank ℝ E : ℝ) * (1 / (1 - δ))) ^ 2 := by
  classical
  set R : ℝ := 1 / (1 - δ) with hR
  have hcoeff : 0 < 1 - δ := by linarith
  have hRnn : 0 ≤ R := by rw [hR]; positivity
  set fA : TangentSpace I x :=
    inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 3))) with hfA
  set fC : TangentSpace I x :=
    inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 1))) with hfC
  set A : ℝ := g₀.inner x (e (K 0)) fA with hA
  set C : ℝ := g₀.inner x (e (K 0)) fC with hC
  have hAbound : |A| ≤ R := by
    rw [hA, hR, hfA]
    refine abs_g0_inner_invSharp_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x (e (K 0)) (e (K 3)) ?_ ?_
    · rw [horth (K 0) (K 0)]; simp
    · rw [horth (K 3) (K 3)]; simp
  have hCbound : |C| ≤ R := by
    rw [hC, hR, hfC]
    refine abs_g0_inner_invSharp_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x (e (K 0)) (e (K 1)) ?_ ?_
    · rw [horth (K 0) (K 0)]; simp
    · rw [horth (K 1) (K 1)]; simp
  have hcomp : ∀ J : Fin 2 → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          TensorRSSpace.ofCLM (ricciDeTurckPrincipalCoeffAtPoint (I := I) g₁ x))
        (Module.finrank ℝ E) e K J =
      (1 / 2 : ℝ) *
        (A * ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0))
          + A * ((if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0))
          - C * ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) := by
    intro J
    have hread : fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          TensorRSSpace.ofCLM (ricciDeTurckPrincipalCoeffAtPoint (I := I) g₁ x))
        (Module.finrank ℝ E) e K J =
        Tensor0SSpace.toModel
          ((ricciDeTurckPrincipalCoeffAtPoint (I := I) g₁ x) (coframeS (I := I) (M := M) g₀ x 4 e K))
          (fun k => e (J k)) := by
      unfold fiberNormSqComponent coframeS; rfl
    rw [hread, ricciArmPrincipalCoeffFib_toModel,
      ricciPrincipalCoeffDoubleTraceModel_apply (E := E) (cometricLmodel (I := I) g₁ x) _ (fun k => e (J k))]
    have hev : ∀ (v : Fin 4 → E),
        Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K) v =
          ∏ i : Fin 4, g₀.inner x (e (K i)) (v i) :=
      fun v => coframeS_apply (I := I) (M := M) g₀ x 4 e K v
    have hterm : ∀ k : Fin (Module.finrank ℝ E),
        (Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K)
            (Fin.cons (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))
              ![e (J 0), e (J 1), (Module.finBasis ℝ E) k])
          + Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K)
              (Fin.cons (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                ![e (J 1), e (J 0), (Module.finBasis ℝ E) k])
          - Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K)
              (Fin.cons (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k)))
                (Fin.cons ((Module.finBasis ℝ E) k) (fun l => e (J l))))) =
          g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) *
                (g₀.inner x (e (K 1)) (e (J 0)) * g₀.inner x (e (K 2)) (e (J 1))))
          + g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) *
                (g₀.inner x (e (K 1)) (e (J 1)) * g₀.inner x (e (K 2)) (e (J 0))))
          - g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) *
              (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) *
                (g₀.inner x (e (K 2)) (e (J 0)) * g₀.inner x (e (K 3)) (e (J 1)))) := by
      intro k
      have hthird : (Fin.cons ((Module.finBasis ℝ E) k) (fun l : Fin 2 => e (J l)) :
          Fin 3 → E) = ![(Module.finBasis ℝ E) k, e (J 0), e (J 1)] := by
        funext i; fin_cases i <;> rfl
      rw [hev, hev, hev, hthird, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_four]
      have hcons4 : ∀ (c : E) (a b d : E),
          (Fin.cons c ![a, b, d] : Fin 4 → E) 0 = c ∧
          (Fin.cons c ![a, b, d] : Fin 4 → E) 1 = a ∧
          (Fin.cons c ![a, b, d] : Fin 4 → E) 2 = b ∧
          (Fin.cons c ![a, b, d] : Fin 4 → E) 3 = d := by
        intro c a b d
        refine ⟨rfl, ?_, ?_, ?_⟩ <;> rfl
      obtain ⟨t1_0, t1_1, t1_2, t1_3⟩ := hcons4 (cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) (e (J 0)) (e (J 1)) ((Module.finBasis ℝ E) k)
      obtain ⟨t2_0, t2_1, t2_2, t2_3⟩ := hcons4 (cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) (e (J 1)) (e (J 0)) ((Module.finBasis ℝ E) k)
      obtain ⟨t3_0, t3_1, t3_2, t3_3⟩ := hcons4 (cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))) ((Module.finBasis ℝ E) k) (e (J 0)) (e (J 1))
      rw [t1_0, t1_1, t1_2, t1_3, t2_0, t2_1, t2_2, t2_3, t3_0, t3_1, t3_2, t3_3]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hcolA : (∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
            (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) *
              (g₀.inner x (e (K 1)) (e (J 0)) * g₀.inner x (e (K 2)) (e (J 1)))))
        = A * (g₀.inner x (e (K 1)) (e (J 0)) * g₀.inner x (e (K 2)) (e (J 1))) := by
      rw [show (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) *
                (g₀.inner x (e (K 1)) (e (J 0)) * g₀.inner x (e (K 2)) (e (J 1))))) =
          (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))) *
            (g₀.inner x (e (K 1)) (e (J 0)) * g₀.inner x (e (K 2)) (e (J 1))) from by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => ?_); ring]
      rw [cometric_dualsum_inner_collapse (I := I) g₀ g₁ x (e (K 0)) (e (K 3)), ← hfA, ← hA]
    have hcolB : (∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
            (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) *
              (g₀.inner x (e (K 1)) (e (J 1)) * g₀.inner x (e (K 2)) (e (J 0)))))
        = A * (g₀.inner x (e (K 1)) (e (J 1)) * g₀.inner x (e (K 2)) (e (J 0))) := by
      rw [show (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) *
                (g₀.inner x (e (K 1)) (e (J 1)) * g₀.inner x (e (K 2)) (e (J 0))))) =
          (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))) *
            (g₀.inner x (e (K 1)) (e (J 1)) * g₀.inner x (e (K 2)) (e (J 0))) from by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => ?_); ring]
      rw [cometric_dualsum_inner_collapse (I := I) g₀ g₁ x (e (K 0)) (e (K 3)), ← hfA, ← hA]
    have hcolC : (∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) *
            (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) *
              (g₀.inner x (e (K 2)) (e (J 0)) * g₀.inner x (e (K 3)) (e (J 1)))))
        = C * (g₀.inner x (e (K 2)) (e (J 0)) * g₀.inner x (e (K 3)) (e (J 1))) := by
      rw [show (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) *
              (g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) *
                (g₀.inner x (e (K 2)) (e (J 0)) * g₀.inner x (e (K 3)) (e (J 1))))) =
          (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) *
              g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))) *
            (g₀.inner x (e (K 2)) (e (J 0)) * g₀.inner x (e (K 3)) (e (J 1))) from by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun k _ => ?_); ring]
      rw [cometric_dualsum_inner_collapse (I := I) g₀ g₁ x (e (K 0)) (e (K 1)), ← hfC, ← hC]
    rw [hcolA, hcolB, hcolC, horth (K 1) (J 0), horth (K 2) (J 1), horth (K 1) (J 1),
      horth (K 2) (J 0), horth (K 3) (J 1)]
  rw [Finset.sum_congr rfl (fun J _ => by rw [hcomp J])]
  have hbound9 : (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        ((1 / 2 : ℝ) *
          (A * ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0))
            + A * ((if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0))
            - C * ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)))) ^ 2)
      ≤ ((Module.finrank ℝ E : ℝ) * R) ^ 2 := by
    rcases Nat.lt_or_ge (Module.finrank ℝ E) 2 with hlt2 | hge2
    · have hfr : Module.finrank ℝ E = 1 := by
        have h1 : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
        omega
      have hAeqC : A = C := by
        have hsub : Subsingleton (Fin (Module.finrank ℝ E)) := by rw [hfr]; infer_instance
        have hK13 : K 1 = K 3 := Subsingleton.elim _ _
        rw [hA, hC, hfA, hfC, hK13]
      refine (ricciArm_dim1_compSq_le (A := A) (C := C) (R := R) hAbound hAeqC hfr
        (K := K)).trans ?_
      have hfrR : (Module.finrank ℝ E : ℝ) = 1 := by rw [hfr]; norm_num
      rw [hfrR]; rw [one_mul]
    · have hstep : (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
            ((1 / 2 : ℝ) *
              (A * ((if K 1 = J 0 then (1 : ℝ) else 0) * (if K 2 = J 1 then (1 : ℝ) else 0))
                + A * ((if K 1 = J 1 then (1 : ℝ) else 0) * (if K 2 = J 0 then (1 : ℝ) else 0))
                - C * ((if K 2 = J 0 then (1 : ℝ) else 0) *
                  (if K 3 = J 1 then (1 : ℝ) else 0)))) ^ 2)
          ≤ (9 / 4 : ℝ) * R ^ 2 :=
        (Finset.sum_le_sum (fun J _ =>
          ricciArm_compSq_le_indicator (A := A) (C := C) (R := R) hAbound hCbound
            (K := K) (J := J))).trans (ricciArm_indicatorSum_le (K := K) (R := R))
      refine hstep.trans ?_
      have hge2R : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hge2
      have hfin2 : (4 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 := by nlinarith [hge2R]
      nlinarith [hfin2, hRnn, sq_nonneg R, mul_le_mul_of_nonneg_right hfin2 (sq_nonneg R)]
  exact hbound9

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_ricciArmPrincipalCoeffFib_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (show TensorRSSpace 4 2 I x from
          TensorRSSpace.ofCLM (ricciDeTurckPrincipalCoeffAtPoint (I := I) g₁ x))
      ≤ ((Module.finrank ℝ E : ℝ) ^ 3 * (1 / (1 - δ))) ^ 2 := by
  have hbound := riemannianFiberNormSq_le_of_orthonormalFrame_componentSumSq_le (I := I) (M := M) g₀ 4 2 x
    (show TensorRSSpace 4 2 I x from
      TensorRSSpace.ofCLM (ricciDeTurckPrincipalCoeffAtPoint (I := I) g₁ x))
    ((Module.finrank ℝ E : ℝ) * (1 / (1 - δ)))
    (fun e horth K =>
      ricciArmPrincipalCoeffFib_fiberComponent_Ksum_sq_le (I := I) (M := M) g₀ g₁ h htie hδ_lt
        hδ_nn hδ x e horth K)
  refine hbound.trans (le_of_eq ?_)
  ring

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem traceHessianFib_fiberComponent_Ksum_sq_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 4 → Fin (Module.finrank ℝ E)) :
    (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x)
        (Module.finrank ℝ E) e K J) ^ 2)
      ≤ ((Module.finrank ℝ E : ℝ) * (1 / (1 - δ))) ^ 2 := by
  classical
  set R : ℝ := 1 / (1 - δ) with hR
  set fK3 : TangentSpace I x :=
    inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 3))) with hfK3
  have hcomp : ∀ J : Fin 2 → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x) (Module.finrank ℝ E) e K J =
      (if K 0 = J 0 then (1 : ℝ) else 0) * (if K 1 = J 1 then (1 : ℝ) else 0) *
        g₀.inner x (e (K 2)) fK3 := by
    intro J
    have hread : fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x) (Module.finrank ℝ E) e K J =
        Tensor0SSpace.toModel
          ((traceHessianFib (I := I) g₁ x) (coframeS (I := I) (M := M) g₀ x 4 e K))
          (fun k => e (J k)) := by
      unfold fiberNormSqComponent coframeS; rfl
    rw [hread, traceHessianFib_toModel]
    rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₁ x) _ (fun k => e (J k))]
    have hterm : ∀ k : Fin (Module.finrank ℝ E),
        (ContinuousMultilinearMap.domDomCongr traceHessianSlotPerm
            (Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K)))
          (Fin.cons (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))
            (Fin.cons ((Module.finBasis ℝ E) k) (fun l => e (J l)))) =
          g₀.inner x (e (K 0)) (e (J 0)) * g₀.inner x (e (K 1)) (e (J 1)) *
            (g₀.inner x (e (K 2)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) *
              g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k)) := by
      intro k
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      set base : Fin 4 → E :=
        Fin.cons (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) (fun l => e (J l))) with hbase
      have hcfeval : Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K)
            (fun i => base (traceHessianSlotPerm i)) =
          ∏ i : Fin 4, g₀.inner x (e (K i)) (base (traceHessianSlotPerm i)) :=
        coframeS_apply (I := I) (M := M) g₀ x 4 e K (fun i => base (traceHessianSlotPerm i))
      rw [hcfeval, Fin.prod_univ_four]
      have hp0 : traceHessianSlotPerm 0 = 2 := by decide
      have hp1 : traceHessianSlotPerm 1 = 3 := by decide
      have hp2 : traceHessianSlotPerm 2 = 0 := by decide
      have hp3 : traceHessianSlotPerm 3 = 1 := by decide
      have hb0 : base 0 = cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)) := by rw [hbase, Fin.cons_zero]
      have hb1 : base 1 = (Module.finBasis ℝ E) k := by
        rw [hbase]
        rw [show (1 : Fin 4) = Fin.succ 0 from rfl, Fin.cons_succ, Fin.cons_zero]
      have hb2 : base 2 = e (J 0) := by
        rw [hbase]
        rw [show (2 : Fin 4) = Fin.succ 1 from rfl, Fin.cons_succ,
          show (1 : Fin 3) = Fin.succ 0 from rfl, Fin.cons_succ]
      have hb3 : base 3 = e (J 1) := by
        rw [hbase]
        rw [show (3 : Fin 4) = Fin.succ 2 from rfl, Fin.cons_succ,
          show (2 : Fin 3) = Fin.succ 1 from rfl, Fin.cons_succ]
      rw [hp0, hp1, hp2, hp3, hb0, hb1, hb2, hb3]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [show (∑ k : Fin (Module.finrank ℝ E),
        g₀.inner x (e (K 0)) (e (J 0)) * g₀.inner x (e (K 1)) (e (J 1)) *
          (g₀.inner x (e (K 2)) (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k))) *
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k))) =
        g₀.inner x (e (K 0)) (e (J 0)) * g₀.inner x (e (K 1)) (e (J 1)) *
          (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              g₀.inner x (e (K 2)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k)))) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_); ring]
    have hcollapse : (∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
            g₀.inner x (e (K 2)) (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))) =
        g₀.inner x (e (K 2)) fK3 := by
      have hsumeq : (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) •
              cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) = fK3 := by
        rw [hfK3]; exact cometric_sum_eq_invSharp (I := I) g₀ g₁ x (e (K 3))
      calc (∑ k : Fin (Module.finrank ℝ E),
            g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) *
              g₀.inner x (e (K 2)) (cometricLmodel (I := I) g₁ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))))
          = ∑ k : Fin (Module.finrank ℝ E), g₀.inner x (e (K 2))
              (g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) •
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [ContinuousLinearMap.map_smul, smul_eq_mul]
        _ = g₀.inner x (e (K 2))
              (∑ k : Fin (Module.finrank ℝ E), g₀.inner x (e (K 3)) ((Module.finBasis ℝ E) k) •
                cometricLmodel (I := I) g₁ x
                  (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                    ((Module.finBasis ℝ E).cDualBasis k))) := (map_sum (g₀.inner x (e (K 2))) _ _).symm
        _ = g₀.inner x (e (K 2)) fK3 := by rw [hsumeq]
    rw [hcollapse, horth (K 0) (J 0), horth (K 1) (J 1)]
  rw [Finset.sum_congr rfl (fun J _ => by rw [hcomp J])]
  have hKbound : |g₀.inner x (e (K 2)) fK3| ≤ R := by
    rw [hR, hfK3]
    refine abs_g0_inner_invSharp_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x (e (K 2)) (e (K 3)) ?_ ?_
    · rw [horth (K 2) (K 2)]; simp
    · rw [horth (K 3) (K 3)]; simp
  have hsingle : (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        ((if K 0 = J 0 then (1 : ℝ) else 0) * (if K 1 = J 1 then (1 : ℝ) else 0) *
          g₀.inner x (e (K 2)) fK3) ^ 2)
      ≤ g₀.inner x (e (K 2)) fK3 ^ 2 := by
    have hbij : (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
          ((if K 0 = J 0 then (1 : ℝ) else 0) * (if K 1 = J 1 then (1 : ℝ) else 0) *
            g₀.inner x (e (K 2)) fK3) ^ 2)
        = ∑ j0 : Fin (Module.finrank ℝ E), ∑ j1 : Fin (Module.finrank ℝ E),
            ((if K 0 = j0 then (1 : ℝ) else 0) * (if K 1 = j1 then (1 : ℝ) else 0) *
              g₀.inner x (e (K 2)) fK3) ^ 2 := by
      rw [← (finTwoArrowEquiv (Fin (Module.finrank ℝ E))).symm.sum_comp
        (fun J : Fin 2 → Fin (Module.finrank ℝ E) =>
          ((if K 0 = J 0 then (1 : ℝ) else 0) * (if K 1 = J 1 then (1 : ℝ) else 0) *
            g₀.inner x (e (K 2)) fK3) ^ 2)]
      rw [Fintype.sum_prod_type]; rfl
    rw [hbij]
    have hcollapse2 : ∀ j0 j1 : Fin (Module.finrank ℝ E),
        ((if K 0 = j0 then (1 : ℝ) else 0) * (if K 1 = j1 then (1 : ℝ) else 0) *
          g₀.inner x (e (K 2)) fK3) ^ 2 =
        (if K 0 = j0 then (1 : ℝ) else 0) * (if K 1 = j1 then (1 : ℝ) else 0) *
          g₀.inner x (e (K 2)) fK3 ^ 2 := by
      intro j0 j1
      by_cases h0 : K 0 = j0 <;> by_cases h1 : K 1 = j1 <;> simp [h0, h1]
    rw [Finset.sum_congr rfl (fun j0 _ => Finset.sum_congr rfl (fun j1 _ => hcollapse2 j0 j1))]
    have hinner : ∀ j0 : Fin (Module.finrank ℝ E),
        (∑ j1 : Fin (Module.finrank ℝ E),
          (if K 0 = j0 then (1 : ℝ) else 0) * (if K 1 = j1 then (1 : ℝ) else 0) *
            g₀.inner x (e (K 2)) fK3 ^ 2)
        = (if K 0 = j0 then (1 : ℝ) else 0) * (g₀.inner x (e (K 2)) fK3 ^ 2) := by
      intro j0
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [Finset.sum_ite_eq Finset.univ (K 1) (fun _ => (1 : ℝ))]
      simp
    rw [Finset.sum_congr rfl (fun j0 _ => hinner j0)]
    rw [← Finset.sum_mul, Finset.sum_ite_eq Finset.univ (K 0) (fun _ => (1 : ℝ))]
    simp
  refine hsingle.trans ?_
  have hcoeff : 0 < 1 - δ := by linarith
  have hRnn : 0 ≤ R := by rw [hR]; positivity
  have hKsq : g₀.inner x (e (K 2)) fK3 ^ 2 ≤ R ^ 2 := by
    have habs := sq_abs (g₀.inner x (e (K 2)) fK3)
    nlinarith [hKbound, abs_nonneg (g₀.inner x (e (K 2)) fK3)]
  refine hKsq.trans ?_
  have hn_ge : (1 : ℝ) ≤ ((Module.finrank ℝ E : ℝ)) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Module.finrank ℝ E))
  have hRle : R ≤ ((Module.finrank ℝ E : ℝ)) * R := by
    nlinarith [mul_le_mul_of_nonneg_right hn_ge hRnn]
  have hfinR_nn : 0 ≤ ((Module.finrank ℝ E : ℝ)) * R := by positivity
  nlinarith [hRle, hRnn, hfinR_nn, mul_le_mul hRle hRle hRnn hfinR_nn]

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_traceHessianFib_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        (show TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x)
      ≤ ((Module.finrank ℝ E : ℝ) ^ 3 * (1 / (1 - δ))) ^ 2 := by
  have hbound := riemannianFiberNormSq_le_of_orthonormalFrame_componentSumSq_le (I := I) (M := M) g₀ 4 2 x
    (show TensorRSSpace 4 2 I x from traceHessianFib (I := I) g₁ x)
    ((Module.finrank ℝ E : ℝ) * (1 / (1 - δ)))
    (fun e horth K =>
      traceHessianFib_fiberComponent_Ksum_sq_le (I := I) (M := M) g₀ g₁ h htie hδ_lt
        hδ_nn hδ x e horth K)
  refine hbound.trans (le_of_eq ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cometricDoubleTraceFib_fiberComponent_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 3 → Fin (Module.finrank ℝ E)) (J : Fin 1 → Fin (Module.finrank ℝ E)) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 3 1
        (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x)
        (Module.finrank ℝ E) e K J =
      (if K 2 = J 0 then (1 : ℝ) else 0) *
        g₀.inner x (e (K 0))
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 1)))) := by
  classical
  have hread : fiberNormSqComponent (I := I) (M := M) g₀ x 3 1
        (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x)
        (Module.finrank ℝ E) e K J =
      Tensor0SSpace.toModel
        ((cometricDoubleTraceFib (I := I) g₁ 1 x) (coframeS (I := I) (M := M) g₀ x 3 e K))
        (fun k => e (J k)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hread, cometricDoubleTraceFib_toModel]
  rw [modelDoubleTrace_apply (E := E) 1 (cometricLmodel (I := I) g₁ x) _ (fun k => e (J k))]
  have hterm : ∀ k : Fin (Module.finrank ℝ E),
      Tensor0SBundle.Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 3 e K)
        (Fin.cons (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)))
          (Fin.cons ((Module.finBasis ℝ E) k) (fun l => e (J l)))) =
        g₀.inner x (e (K 2)) (e (J 0)) *
          (g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) *
            g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))) := by
    intro k
    set base : Fin 3 → E :=
      Fin.cons (cometricLmodel (I := I) g₁ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k)))
        (Fin.cons ((Module.finBasis ℝ E) k) (fun l => e (J l))) with hbase
    have hcfeval : Tensor0SBundle.Tensor0SSpace.toModel
          (coframeS (I := I) (M := M) g₀ x 3 e K) base =
        ∏ i : Fin 3, g₀.inner x (e (K i)) (base i) :=
      coframeS_apply (I := I) (M := M) g₀ x 3 e K base
    rw [hcfeval, Fin.prod_univ_three]
    have hb0 : base 0 = cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k)) := by rw [hbase, Fin.cons_zero]
    have hb1 : base 1 = (Module.finBasis ℝ E) k := by
      rw [hbase, show (1 : Fin 3) = Fin.succ 0 from rfl, Fin.cons_succ, Fin.cons_zero]
    have hb2 : base 2 = e (J 0) := by
      rw [hbase, show (2 : Fin 3) = Fin.succ 1 from rfl, Fin.cons_succ,
        show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cons_succ]
    rw [hb0, hb1, hb2]; ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  have hpull : (∑ k : Fin (Module.finrank ℝ E),
      g₀.inner x (e (K 2)) (e (J 0)) *
        (g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) *
          g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))))) =
      g₀.inner x (e (K 2)) (e (J 0)) *
        (∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) *
            g₀.inner x (e (K 0)) (cometricLmodel (I := I) g₁ x
              (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                ((Module.finBasis ℝ E).cDualBasis k)))) := by
    rw [Finset.mul_sum]
  rw [hpull, cometric_dualsum_inner_collapse (I := I) g₀ g₁ x (e (K 0)) (e (K 1)),
    horth (K 2) (J 0)]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma cometricDoubleTraceFib_fiberComponent_Ksum_sq_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 3 → Fin (Module.finrank ℝ E)) :
    (∑ J : Fin 1 → Fin (Module.finrank ℝ E),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 3 1
        (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x)
        (Module.finrank ℝ E) e K J) ^ 2)
      ≤ (1 / (1 - δ)) ^ 2 := by
  classical
  set R : ℝ := 1 / (1 - δ) with hR
  set q : ℝ := g₀.inner x (e (K 0))
    (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e (K 1)))) with hq
  have hqbound : |q| ≤ R := by
    rw [hR, hq]
    refine abs_g0_inner_invSharp_le (I := I) g₀ g₁ h htie hδ_lt hδ_nn hδ x
      (e (K 0)) (e (K 1)) ?_ ?_
    · rw [horth (K 0) (K 0)]; simp
    · rw [horth (K 1) (K 1)]; simp
  have hcomp : ∀ J : Fin 1 → Fin (Module.finrank ℝ E),
      fiberNormSqComponent (I := I) (M := M) g₀ x 3 1
        (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x)
        (Module.finrank ℝ E) e K J =
      (if K 2 = J 0 then (1 : ℝ) else 0) * q := by
    intro J
    rw [cometricDoubleTraceFib_fiberComponent_eq (I := I) g₀ g₁ x e horth K J, hq]
  rw [Finset.sum_congr rfl (fun J _ => by rw [hcomp J])]
  have hsingle : (∑ J : Fin 1 → Fin (Module.finrank ℝ E),
        ((if K 2 = J 0 then (1 : ℝ) else 0) * q) ^ 2) ≤ q ^ 2 := by
    have hbij : (∑ J : Fin 1 → Fin (Module.finrank ℝ E),
          ((if K 2 = J 0 then (1 : ℝ) else 0) * q) ^ 2)
        = ∑ j0 : Fin (Module.finrank ℝ E),
            ((if K 2 = j0 then (1 : ℝ) else 0) * q) ^ 2 := by
      apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin (Module.finrank ℝ E)))
      intro J; rfl
    rw [hbij]
    have hcollapse : ∀ j0 : Fin (Module.finrank ℝ E),
        ((if K 2 = j0 then (1 : ℝ) else 0) * q) ^ 2 =
        (if K 2 = j0 then (1 : ℝ) else 0) * q ^ 2 := by
      intro j0
      by_cases h0 : K 2 = j0 <;> simp [h0]
    rw [Finset.sum_congr rfl (fun j0 _ => hcollapse j0)]
    rw [← Finset.sum_mul, Finset.sum_ite_eq Finset.univ (K 2) (fun _ => (1 : ℝ))]
    simp
  refine hsingle.trans ?_
  have hcoeff : 0 < 1 - δ := by linarith
  have hRnn : 0 ≤ R := by rw [hR]; positivity
  have hqsq : q ^ 2 ≤ R ^ 2 := by
    have habs := sq_abs q
    nlinarith [hqbound, abs_nonneg q]
  exact hqsq

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_cometricDoubleTraceFib_le
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (h : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + h y v w)
    {δ : ℝ} (hδ_lt : δ < 1) (hδ_nn : 0 ≤ δ)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 1 x
        (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x)
      ≤ ((Module.finrank ℝ E : ℝ) ^ 3) * (1 / (1 - δ)) ^ 2 := by
  exact riemannianFiberNormSq_le_of_orthonormalFrame_componentSumSq_le (I := I) (M := M) g₀ 3 1 x
    (show TensorRSSpace 3 1 I x from cometricDoubleTraceFib (I := I) g₁ 1 x)
    (1 / (1 - δ))
    (fun e horth K =>
      cometricDoubleTraceFib_fiberComponent_Ksum_sq_le (I := I) g₀ g₁ h htie hδ_lt
        hδ_nn hδ x e horth K)

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
