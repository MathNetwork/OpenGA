import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PerturbedCurvatureOperatorBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpHigherRankParseval
import DifferentialGeometry.Geometry.Metric.MetricBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.PerturbedInnerUpperBound


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private lemma inv_le_inv_of_le_of_pos {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    a⁻¹ ≤ b⁻¹ := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  rw [inv_le_inv₀ ha hb]; exact hab

omit [FiniteDimensional ℝ E] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem orthoFrame_to_basis
    (g : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    ∃ bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x),
      ∀ i : Fin (Module.finrank ℝ E), bse i = e i := by
  classical
  haveI : Nonempty (Fin (Module.finrank ℝ (TangentSpace I x))) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hcard : Fintype.card (Fin (Module.finrank ℝ (TangentSpace I x))) =
      Module.finrank ℝ (TangentSpace I x) := Fintype.card_fin _
  refine ⟨basisOfLinearIndependentOfCardEqFinrank he_li hcard, fun i => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem componentSlice_sq_sum_le_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (x : M) (S : TensorRSSpace 2 2 I x)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ a b : Fin (Module.finrank ℝ E),
      g.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K : Fin 2 → Fin (Module.finrank ℝ E)) :
    (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
      (fiberNormSqComponent (I := I) (M := M) g x 2 2 S
        (Module.finrank ℝ E) e K J) ^ 2) ≤
      riemannianFiberNormSq (I := I) (M := M) g 2 2 x S := by
  classical
  obtain ⟨bse, hbse⟩ := orthoFrame_to_basis (I := I) (M := M) g x e horth
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g 2 2 x S e bse rfl hbse horth]
  refine Finset.single_le_sum
    (f := fun K' : Fin 2 → Fin (Module.finrank ℝ E) =>
      ∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        (fiberNormSqComponent (I := I) (M := M) g x 2 2 S (Module.finrank ℝ E) e K' J) ^ 2)
    (fun K' _ => Finset.sum_nonneg (fun J _ => sq_nonneg _)) (Finset.mem_univ K)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem riemannianFiberNormSq_le_of_componentSlice_sq_sum_le
    (g₀ : SmoothRiemannianMetric I M) (x : M) (S : TensorRSSpace 2 2 I x) (C : ℝ)
    (_hC : 0 ≤ C)
    (hslice : ∀ (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
      (_horth : ∀ a b : Fin (Module.finrank ℝ E),
        g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
      (K : Fin 2 → Fin (Module.finrank ℝ E)),
      (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
        (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2 S (Module.finrank ℝ E) e K J) ^ 2)
        ≤ C ^ 2) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x S ≤
      ((Module.finrank ℝ E : ℝ) ^ 2) * C ^ 2 := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hexpand, _hrepr⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E :=
    hn.trans (by rfl)
  subst hnE
  have horth' : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0 := horth
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 2 2 x S e bse rfl hbse horth']
  calc (∑ K : Fin 2 → Fin (Module.finrank ℝ E), ∑ J : Fin 2 → Fin (Module.finrank ℝ E),
          (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2 S (Module.finrank ℝ E) e K J) ^ 2)
      ≤ ∑ _K : Fin 2 → Fin (Module.finrank ℝ E), C ^ 2 :=
        Finset.sum_le_sum (fun K _ => hslice e horth' K)
    _ = ((Module.finrank ℝ E : ℝ) ^ 2) * C ^ 2 := by
        rw [Finset.sum_const]
        simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_pow]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma riemannBiContr_fiberComponent_expand
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (K J : Fin 2 → Fin (Module.finrank ℝ E)) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))
        (Module.finrank ℝ E) e K J =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₁.inner x
            (riemannOp (cov := LeviCivita (I := I) g₁) x (e (J 0))
              (smoothOrthoFrame (I := I) g₁ x a x)
              (smoothOrthoFrame (I := I) g₁ x b x))
            (e (J 1)) *
          (g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x a x) *
            g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x b x)) := by
  classical
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))
      (Module.finrank ℝ E) e K J =
      Tensor0SSpace.toModel
        ((riemannBiContrFib (I := I) g₁ x)
          (coframeS (I := I) (M := M) g₀ x 2 e K))
        (fun i => (e (J i) : E)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hcomp]
  rw [show (riemannBiContrFib (I := I) g₁ x) = riemannBiContrFibFixedFrame (I := I) g₁
      (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [riemannBiContrFibFixedFrame_toModel]
  refine congrArg (fun t => (2 : ℝ) * t) ?_
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  congr 1
  rw [show (coframeS (I := I) (M := M) g₀ x 2 e K).toModel
        ![(smoothOrthoFrame (I := I) g₁ x a x : E), (smoothOrthoFrame (I := I) g₁ x b x : E)]
      = coframeS (I := I) (M := M) g₀ x 2 e K
        ![smoothOrthoFrame (I := I) g₁ x a x, smoothOrthoFrame (I := I) g₁ x b x] from rfl]
  rw [coframeS_apply, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] in
private lemma g_inner_off_frame_le
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (k : Fin n) (w : TangentSpace I x) {r : ℝ}
    (hw : g₀.inner x w w ≤ r) :
    |g₀.inner x (e k) w| ≤ Real.sqrt r := by
  have hCS := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e k) w
  have hkk : g₀.inner x (e k) (e k) = 1 := by rw [horth k k]; simp
  rw [hkk, Real.sqrt_one, one_mul] at hCS
  exact le_trans hCS (Real.sqrt_le_sqrt hw)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_riemannBiContrFib_perturbed_frameComponentSlice_sq_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ max δ₀ 0)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
          ∀ (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
            (_horth : ∀ a b : Fin (Module.finrank ℝ E),
              g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
            (K : Fin 2 → Fin (Module.finrank ℝ E)),
            (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
              (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
                (show TensorRSSpace 2 2 I x from
                  TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))
                (Module.finrank ℝ E) e K J) ^ 2) ≤ C ^ 2 := by
  classical
  obtain ⟨C0, hC0_nn, hC0⟩ :=
    exists_riemannOp_LeviCivita_perturbed_gQuadratic_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  set m : ℝ := max δ₀ 0 with hm_def
  have hm0 : 0 ≤ m := le_max_right _ _
  have hm1 : m < 1 := max_lt hδ₀ (by norm_num)
  have hmpos : 0 < 1 - m := by linarith
  have hm_inv_nn : (0 : ℝ) ≤ (1 - m)⁻¹ := inv_nonneg.mpr (le_of_lt hmpos)
  set N : ℝ := (Module.finrank ℝ E : ℝ) with hN_def
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
    rw [hN_def]; exact_mod_cast this
  have hN0 : (0 : ℝ) ≤ N := by linarith
  set Ccomp : ℝ := 2 * N ^ 2 * ((1 + m) ^ 2 * C0 * (1 - m)⁻¹) * (1 - m)⁻¹ with hCcomp_def
  have h1m_nn : (0 : ℝ) ≤ 1 + m := by linarith
  have hCcomp_nn : 0 ≤ Ccomp := by
    rw [hCcomp_def]
    have hpre : 0 ≤ (1 + m) ^ 2 * C0 * (1 - m)⁻¹ :=
      mul_nonneg (mul_nonneg (by positivity) hC0_nn) hm_inv_nn
    have h2N : 0 ≤ 2 * N ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg h2N hpre) hm_inv_nn
  refine ⟨N * Ccomp, mul_nonneg hN0 hCcomp_nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv e horth K
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hm1
  have hδ_inv_nn : (0 : ℝ) ≤ (1 - δ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hg1δ : ∀ v : TangentSpace I x, g₁.inner x v v ≤ (1 + δ) * g₀.inner x v v := by
    intro v
    have h := gInner_self_le_of_gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ P) hδ x v
    rw [← htie x v v] at h; exact h
  have hframe_g0 : ∀ a : Fin (Module.finrank ℝ E),
      g₀.inner x (smoothOrthoFrame (I := I) g₁ x a x)
        (smoothOrthoFrame (I := I) g₁ x a x) ≤ (1 - δ)⁻¹ := by
    intro a
    refine gZeroInner_self_le_neumann_of_g1_unit (I := I) (M := M) g₀ g₁ P hδ_lt hδ htie x _ ?_
    rw [show g₁.inner x (smoothOrthoFrame (I := I) g₁ x a x)
          (smoothOrthoFrame (I := I) g₁ x a x)
        = if a = a then (1 : ℝ) else 0 from
      smoothOrthoFrame_orthonormal_at_center (I := I) g₁ x a a]
    simp
  have hgterm : ∀ (a b : Fin (Module.finrank ℝ E)),
      |g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x a x)
          * g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x b x)|
        ≤ (1 - m)⁻¹ := by
    intro a b
    have hinv_le : (1 - δ)⁻¹ ≤ (1 - m)⁻¹ :=
      inv_le_inv_of_le_of_pos hmpos (by linarith)
    have hinv_nn : (0 : ℝ) ≤ (1 - δ)⁻¹ := hδ_inv_nn
    have hsqrt_le : Real.sqrt ((1 - δ)⁻¹) ≤ Real.sqrt ((1 - m)⁻¹) :=
      Real.sqrt_le_sqrt hinv_le
    have hA := g_inner_off_frame_le (I := I) (M := M) g₀ x e horth (K 0)
      (smoothOrthoFrame (I := I) g₁ x a x) (hframe_g0 a)
    have hB := g_inner_off_frame_le (I := I) (M := M) g₀ x e horth (K 1)
      (smoothOrthoFrame (I := I) g₁ x b x) (hframe_g0 b)
    have hsqrt_inv_m : Real.sqrt ((1 - m)⁻¹) * Real.sqrt ((1 - m)⁻¹) = (1 - m)⁻¹ := by
      rw [← Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)]
    rw [abs_mul]
    calc |g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x a x)|
          * |g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x b x)|
        ≤ Real.sqrt ((1 - m)⁻¹) * Real.sqrt ((1 - m)⁻¹) :=
          mul_le_mul (le_trans hA hsqrt_le) (le_trans hB hsqrt_le) (abs_nonneg _)
            (Real.sqrt_nonneg _)
      _ = (1 - m)⁻¹ := hsqrt_inv_m
  have htterm : ∀ (J : Fin 2 → Fin (Module.finrank ℝ E))
      (a b : Fin (Module.finrank ℝ E)),
      |g₁.inner x
          (riemannOp (cov := LeviCivita (I := I) g₁) x (e (J 0))
            (smoothOrthoFrame (I := I) g₁ x a x)
            (smoothOrthoFrame (I := I) g₁ x b x))
          (e (J 1))|
        ≤ (1 + m) ^ 2 * C0 * (1 - m)⁻¹ := by
    intro J a b
    set R := riemannOp (cov := LeviCivita (I := I) g₁) x (e (J 0))
      (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x) with hR
    have hCS := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₁ x R (e (J 1))
    have hg0RR : g₀.inner x R R ≤ C0 ^ 2 * (1 - δ)⁻¹ * (1 - δ)⁻¹ := by
      have hR2 := hC0 g₁ P hδ_le hδ htie x henv (e (J 0))
        (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)
      have hJ0 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
      have hfa := hframe_g0 a
      have hfb := hframe_g0 b
      have hC0sq_nn : 0 ≤ C0 ^ 2 := sq_nonneg _
      have hfa_nn : 0 ≤ g₀.inner x (smoothOrthoFrame (I := I) g₁ x a x)
          (smoothOrthoFrame (I := I) g₁ x a x) :=
        metric_inner_self_nonneg (I := I) (M := M) g₀ x _
      have hfb_nn : 0 ≤ g₀.inner x (smoothOrthoFrame (I := I) g₁ x b x)
          (smoothOrthoFrame (I := I) g₁ x b x) :=
        metric_inner_self_nonneg (I := I) (M := M) g₀ x _
      have hstep_le : C0 ^ 2 * g₀.inner x (e (J 0)) (e (J 0))
              * g₀.inner x (smoothOrthoFrame (I := I) g₁ x a x)
                  (smoothOrthoFrame (I := I) g₁ x a x)
              * g₀.inner x (smoothOrthoFrame (I := I) g₁ x b x)
                  (smoothOrthoFrame (I := I) g₁ x b x)
            ≤ C0 ^ 2 * (1 - δ)⁻¹ * (1 - δ)⁻¹ := by
        rw [hJ0, mul_one]
        have h1 : C0 ^ 2 * g₀.inner x (smoothOrthoFrame (I := I) g₁ x a x)
            (smoothOrthoFrame (I := I) g₁ x a x) ≤ C0 ^ 2 * (1 - δ)⁻¹ :=
          mul_le_mul_of_nonneg_left hfa hC0sq_nn
        have hb_nn : (0 : ℝ) ≤ C0 ^ 2 * (1 - δ)⁻¹ := mul_nonneg hC0sq_nn hδ_inv_nn
        exact mul_le_mul h1 hfb hfb_nn hb_nn
      exact le_trans hR2 hstep_le
    have hg1RR : g₁.inner x R R ≤ (1 + m) * (C0 ^ 2 * (1 - δ)⁻¹ * (1 - δ)⁻¹) := by
      have h := hg1δ R
      have hg0RR_nn : 0 ≤ g₀.inner x R R := metric_inner_self_nonneg (I := I) (M := M) g₀ x R
      have hδm : (1 + δ) ≤ (1 + m) := by linarith
      calc g₁.inner x R R ≤ (1 + δ) * g₀.inner x R R := h
        _ ≤ (1 + m) * g₀.inner x R R :=
            mul_le_mul_of_nonneg_right hδm hg0RR_nn
        _ ≤ (1 + m) * (C0 ^ 2 * (1 - δ)⁻¹ * (1 - δ)⁻¹) :=
            mul_le_mul_of_nonneg_left hg0RR (by linarith)
    have hg1JJ : g₁.inner x (e (J 1)) (e (J 1)) ≤ (1 + m) := by
      have h := hg1δ (e (J 1))
      have hJ1 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by rw [horth (J 1) (J 1)]; simp
      rw [hJ1, mul_one] at h
      linarith
    have hRR_nn : 0 ≤ g₁.inner x R R := metric_inner_self_nonneg (I := I) (M := M) g₁ x R
    have hJJ_nn : 0 ≤ g₁.inner x (e (J 1)) (e (J 1)) :=
      metric_inner_self_nonneg (I := I) (M := M) g₁ x (e (J 1))
    have hbnd1 : (1 + m) * (C0 ^ 2 * (1 - δ)⁻¹ * (1 - δ)⁻¹) ≤
        ((1 + m) * C0 * (1 - m)⁻¹) ^ 2 := by
      have hinv_le : (1 - δ)⁻¹ ≤ (1 - m)⁻¹ := inv_le_inv_of_le_of_pos hmpos (by linarith)
      have hinv_nn : (0 : ℝ) ≤ (1 - δ)⁻¹ := hδ_inv_nn
      have h1m : (1 : ℝ) ≤ 1 + m := by linarith
      have hC0sq_nn : (0 : ℝ) ≤ C0 ^ 2 := sq_nonneg _
      have hinvsq_le : (1 - δ)⁻¹ * (1 - δ)⁻¹ ≤ (1 - m)⁻¹ * (1 - m)⁻¹ :=
        mul_le_mul hinv_le hinv_le hinv_nn hm_inv_nn
      have hstep1 : (1 + m) * (C0 ^ 2 * (1 - δ)⁻¹ * (1 - δ)⁻¹)
          ≤ (1 + m) * (C0 ^ 2 * (1 - m)⁻¹ * (1 - m)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_left hinvsq_le hC0sq_nn
      have hstep2 : (1 + m) * (C0 ^ 2 * (1 - m)⁻¹ * (1 - m)⁻¹)
          ≤ ((1 + m) * C0 * (1 - m)⁻¹) ^ 2 := by
        have hpre_nn : (0 : ℝ) ≤ C0 ^ 2 * (1 - m)⁻¹ * (1 - m)⁻¹ :=
          mul_nonneg (mul_nonneg hC0sq_nn hm_inv_nn) hm_inv_nn
        have hfac : (1 + m) ≤ (1 + m) * (1 + m) := by nlinarith [h1m]
        calc (1 + m) * (C0 ^ 2 * (1 - m)⁻¹ * (1 - m)⁻¹)
            ≤ ((1 + m) * (1 + m)) * (C0 ^ 2 * (1 - m)⁻¹ * (1 - m)⁻¹) :=
              mul_le_mul_of_nonneg_right hfac hpre_nn
          _ = ((1 + m) * C0 * (1 - m)⁻¹) ^ 2 := by ring
      exact le_trans hstep1 hstep2
    have hsqrt_RR : Real.sqrt (g₁.inner x R R) ≤ (1 + m) * C0 * (1 - m)⁻¹ := by
      have hb_nn : 0 ≤ (1 + m) * C0 * (1 - m)⁻¹ :=
        mul_nonneg (mul_nonneg (by linarith) hC0_nn) hm_inv_nn
      have : Real.sqrt (g₁.inner x R R) ≤
          Real.sqrt (((1 + m) * C0 * (1 - m)⁻¹) ^ 2) :=
        Real.sqrt_le_sqrt (le_trans hg1RR hbnd1)
      rwa [Real.sqrt_sq hb_nn] at this
    have hsqrt_JJ : Real.sqrt (g₁.inner x (e (J 1)) (e (J 1))) ≤ Real.sqrt (1 + m) :=
      Real.sqrt_le_sqrt hg1JJ
    have hsqrt_1m_le : Real.sqrt (1 + m) ≤ 1 + m := by
      have h1m : (1 : ℝ) ≤ 1 + m := by linarith
      calc Real.sqrt (1 + m) ≤ Real.sqrt ((1 + m) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [h1m])
        _ = 1 + m := Real.sqrt_sq (by linarith)
    have hsqrtRR_nn : 0 ≤ Real.sqrt (g₁.inner x R R) := Real.sqrt_nonneg _
    have hsqrtJJ_nn : 0 ≤ Real.sqrt (g₁.inner x (e (J 1)) (e (J 1))) := Real.sqrt_nonneg _
    have hRbnd_nn : 0 ≤ (1 + m) * C0 * (1 - m)⁻¹ :=
      mul_nonneg (mul_nonneg (by linarith) hC0_nn) hm_inv_nn
    have hfinal : Real.sqrt (g₁.inner x R R)
        * Real.sqrt (g₁.inner x (e (J 1)) (e (J 1)))
        ≤ (1 + m) ^ 2 * C0 * (1 - m)⁻¹ := by
      have hmul := mul_le_mul hsqrt_RR (le_trans hsqrt_JJ hsqrt_1m_le) hsqrtJJ_nn hRbnd_nn
      have heq : ((1 + m) * C0 * (1 - m)⁻¹) * (1 + m) = (1 + m) ^ 2 * C0 * (1 - m)⁻¹ := by ring
      rw [heq] at hmul
      exact hmul
    exact le_trans hCS hfinal
  have hcomp_abs : ∀ J : Fin 2 → Fin (Module.finrank ℝ E),
      |fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))
          (Module.finrank ℝ E) e K J| ≤ Ccomp := by
    intro J
    rw [riemannBiContr_fiberComponent_expand (I := I) (M := M) g₀ g₁ x e K J]
    rw [abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
    have hsum_abs : |∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          g₁.inner x
              (riemannOp (cov := LeviCivita (I := I) g₁) x (e (J 0))
                (smoothOrthoFrame (I := I) g₁ x a x)
                (smoothOrthoFrame (I := I) g₁ x b x))
              (e (J 1)) *
            (g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x a x) *
              g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x b x))|
        ≤ N ^ 2 * (((1 + m) ^ 2 * C0 * (1 - m)⁻¹) * (1 - m)⁻¹) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hinner : ∀ a : Fin (Module.finrank ℝ E),
          |∑ b : Fin (Module.finrank ℝ E),
              g₁.inner x
                  (riemannOp (cov := LeviCivita (I := I) g₁) x (e (J 0))
                    (smoothOrthoFrame (I := I) g₁ x a x)
                    (smoothOrthoFrame (I := I) g₁ x b x))
                  (e (J 1)) *
                (g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x a x) *
                  g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x b x))|
            ≤ N * (((1 + m) ^ 2 * C0 * (1 - m)⁻¹) * (1 - m)⁻¹) := by
        intro a
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        calc (∑ b : Fin (Module.finrank ℝ E),
              |g₁.inner x
                  (riemannOp (cov := LeviCivita (I := I) g₁) x (e (J 0))
                    (smoothOrthoFrame (I := I) g₁ x a x)
                    (smoothOrthoFrame (I := I) g₁ x b x))
                  (e (J 1)) *
                (g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x a x) *
                  g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x b x))|)
            ≤ ∑ _b : Fin (Module.finrank ℝ E),
                (((1 + m) ^ 2 * C0 * (1 - m)⁻¹) * (1 - m)⁻¹) := by
              refine Finset.sum_le_sum (fun b _ => ?_)
              rw [abs_mul]
              exact mul_le_mul (htterm J a b) (hgterm a b) (abs_nonneg _) (by positivity)
          _ = N * (((1 + m) ^ 2 * C0 * (1 - m)⁻¹) * (1 - m)⁻¹) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hN_def]
      calc (∑ a : Fin (Module.finrank ℝ E),
            |∑ b : Fin (Module.finrank ℝ E),
                g₁.inner x
                    (riemannOp (cov := LeviCivita (I := I) g₁) x (e (J 0))
                      (smoothOrthoFrame (I := I) g₁ x a x)
                      (smoothOrthoFrame (I := I) g₁ x b x))
                    (e (J 1)) *
                  (g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x a x) *
                    g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x b x))|)
          ≤ ∑ _a : Fin (Module.finrank ℝ E),
              (N * (((1 + m) ^ 2 * C0 * (1 - m)⁻¹) * (1 - m)⁻¹)) :=
            Finset.sum_le_sum (fun a _ => hinner a)
        _ = N ^ 2 * (((1 + m) ^ 2 * C0 * (1 - m)⁻¹) * (1 - m)⁻¹) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hN_def]
            ring
    calc (2 : ℝ) * |∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            g₁.inner x
                (riemannOp (cov := LeviCivita (I := I) g₁) x (e (J 0))
                  (smoothOrthoFrame (I := I) g₁ x a x)
                  (smoothOrthoFrame (I := I) g₁ x b x))
                (e (J 1)) *
              (g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x a x) *
                g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x b x))|
        ≤ 2 * (N ^ 2 * (((1 + m) ^ 2 * C0 * (1 - m)⁻¹) * (1 - m)⁻¹)) :=
          mul_le_mul_of_nonneg_left hsum_abs (by norm_num)
      _ = Ccomp := by rw [hCcomp_def]; ring
  calc (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
          (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
            (show TensorRSSpace 2 2 I x from
              TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))
            (Module.finrank ℝ E) e K J) ^ 2)
      ≤ ∑ _J : Fin 2 → Fin (Module.finrank ℝ E), Ccomp ^ 2 := by
        refine Finset.sum_le_sum (fun J _ => ?_)
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hcomp_abs J) 2
    _ = (N * Ccomp) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, hN_def]
        push_cast
        ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_riemannBiContrFib_perturbed_riemannianFiberNormSq_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ max δ₀ 0)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              (show TensorRSSpace 2 2 I x from
                TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) ≤ C ^ 2 := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_riemannBiContrFib_perturbed_frameComponentSlice_sq_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨(Module.finrank ℝ E : ℝ) * C, by positivity, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv
  have hred := riemannianFiberNormSq_le_of_componentSlice_sq_sum_le (I := I) (M := M) g₀ x
    (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x)) C
    hC_nn (fun e horth K => hC g₁ P hδ_le hδ htie x henv e horth K)
  refine le_trans hred (le_of_eq ?_)
  rw [mul_pow]

private lemma slice_indicator_sum_eq_dim {n : ℕ} (K : Fin 2 → Fin n) (k : Fin 2) :
    (∑ J : Fin 2 → Fin n, (if K k = J k then (1 : ℝ) else 0)) = (n : ℝ) := by
  classical
  have hkey : ∀ g : (Fin 2 → Fin n) → ℝ,
      (∑ p : Fin 2 → Fin n, g p) = ∑ a : Fin n, ∑ b : Fin n, g ![a, b] := by
    intro g
    rw [← (finTwoArrowEquiv (Fin n)).symm.sum_comp g, Fintype.sum_prod_type]; rfl
  rw [hkey]
  fin_cases k
  · change (∑ a : Fin n, ∑ b : Fin n,
        (if K 0 = (![a, b] : Fin 2 → Fin n) 0 then (1 : ℝ) else 0)) = (n : ℝ)
    have hinner : ∀ a : Fin n,
        (∑ b : Fin n, (if K 0 = (![a, b] : Fin 2 → Fin n) 0 then (1 : ℝ) else 0))
          = (n : ℝ) * (if K 0 = a then (1 : ℝ) else 0) := by
      intro a
      have : (∑ b : Fin n, (if K 0 = (![a, b] : Fin 2 → Fin n) 0 then (1 : ℝ) else 0))
          = ∑ _b : Fin n, (if K 0 = a then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Matrix.cons_val_zero]
      rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun a _ => hinner a), ← Finset.mul_sum,
      Finset.sum_ite_eq Finset.univ (K 0) (fun _ => (1 : ℝ))]
    simp
  · change (∑ a : Fin n, ∑ b : Fin n,
        (if K 1 = (![a, b] : Fin 2 → Fin n) 1 then (1 : ℝ) else 0)) = (n : ℝ)
    have hinner : ∀ a : Fin n,
        (∑ b : Fin n, (if K 1 = (![a, b] : Fin 2 → Fin n) 1 then (1 : ℝ) else 0)) = 1 := by
      intro a
      have : (∑ b : Fin n, (if K 1 = (![a, b] : Fin 2 → Fin n) 1 then (1 : ℝ) else 0))
          = ∑ b : Fin n, (if K 1 = b then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        congr 1
      rw [this, Finset.sum_ite_eq Finset.univ (K 1) (fun _ => (1 : ℝ))]
      simp
    rw [Finset.sum_congr rfl (fun a _ => hinner a), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma slotEndo_fiberComponent_slotk_eq
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (k : Fin 2) (K J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 k x Λ)) n e K J =
      g₀.inner x (e (K k)) (Λ (e (J k))) *
        ∏ i ∈ Finset.univ.erase k, (if K i = J i then (1 : ℝ) else 0) := by
  classical
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 k x Λ)) n e K J =
      Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) 2 k x Λ) (coframeS (I := I) (M := M) g₀ x 2 e K))
        (fun i => e (J i)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hcomp, slotInsertEndoFib_apply_eval]
  rw [show (coframeS (I := I) (M := M) g₀ x 2 e K).toModel
        (Function.update (fun i => e (J i)) k (Λ (e (J k))))
      = coframeS (I := I) (M := M) g₀ x 2 e K
        (Function.update (fun i => e (J i)) k (Λ (e (J k)))) from rfl]
  rw [coframeS_apply]
  rw [← Finset.prod_erase_mul Finset.univ
    (fun i : Fin 2 => g₀.inner x (e (K i))
      (Function.update (fun i => e (J i)) k (Λ (e (J k))) i)) (Finset.mem_univ k)]
  rw [Function.update_self, mul_comm]
  congr 1
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hik : i ≠ k := Finset.ne_of_mem_erase hi
  rw [Function.update_of_ne hik, horth (K i) (J i)]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma ricciArm_fiberComponent_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (K J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x)) n e K J =
      g₀.inner x (e (K 0)) (ricEndoRaisedFib (I := I) g₁ x (e (J 0))) *
          (if K 1 = J 1 then (1 : ℝ) else 0) +
        g₀.inner x (e (K 1)) (ricEndoRaisedFib (I := I) g₁ x (e (J 1))) *
          (if K 0 = J 0 then (1 : ℝ) else 0) := by
  classical
  have hsplit : (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x)) =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x
          (ricEndoRaisedFib (I := I) g₁ x))) +
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 1 x
            (ricEndoRaisedFib (I := I) g₁ x))) := by
    rfl
  rw [hsplit, fiberNormSqComponent_add,
    slotEndo_fiberComponent_slotk_eq (I := I) (M := M) g₀ x
      (ricEndoRaisedFib (I := I) g₁ x) e horth 0 K J,
    slotEndo_fiberComponent_slotk_eq (I := I) (M := M) g₀ x
      (ricEndoRaisedFib (I := I) g₁ x) e horth 1 K J]
  congr 1
  · rw [show (Finset.univ.erase (0 : Fin 2)) = {1} from by decide]
    rw [Finset.prod_singleton]
  · rw [show (Finset.univ.erase (1 : Fin 2)) = {0} from by decide]
    rw [Finset.prod_singleton]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma ricciArm_component_abs_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hR1 : ∀ v : TangentSpace I x,
      g₀.inner x (ricEndoRaisedFib (I := I) g₁ x v) (ricEndoRaisedFib (I := I) g₁ x v)
        ≤ C ^ 2 * g₀.inner x v v)
    (k : Fin 2) (K J : Fin 2 → Fin n) :
    |g₀.inner x (e (K k)) (ricEndoRaisedFib (I := I) g₁ x (e (J k)))| ≤ C := by
  set Λv : TangentSpace I x := ricEndoRaisedFib (I := I) g₁ x (e (J k)) with hΛv
  have hCS : |g₀.inner x (e (K k)) Λv| ≤
      Real.sqrt (g₀.inner x (e (K k)) (e (K k))) * Real.sqrt (g₀.inner x Λv Λv) :=
    abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (K k)) Λv
  have hKKunit : g₀.inner x (e (K k)) (e (K k)) = 1 := by rw [horth (K k) (K k)]; simp
  have hJJunit : g₀.inner x (e (J k)) (e (J k)) = 1 := by rw [horth (J k) (J k)]; simp
  have hΛnn : 0 ≤ g₀.inner x Λv Λv := metric_inner_self_nonneg (I := I) (M := M) g₀ x Λv
  have hR1k : g₀.inner x Λv Λv ≤ C ^ 2 := by
    have := hR1 (e (J k)); rw [← hΛv, hJJunit, mul_one] at this; exact this
  have hsqrtΛ : Real.sqrt (g₀.inner x Λv Λv) ≤ C := by
    have : Real.sqrt (g₀.inner x Λv Λv) ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt hR1k
    rwa [Real.sqrt_sq hC] at this
  rw [hKKunit, Real.sqrt_one, one_mul] at hCS
  exact le_trans hCS hsqrtΛ

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_ricciArmOrder0CurvCoeffFib_perturbed_frameComponentSlice_sq_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ max δ₀ 0)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
          ∀ (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
            (_horth : ∀ a b : Fin (Module.finrank ℝ E),
              g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
            (K : Fin 2 → Fin (Module.finrank ℝ E)),
            (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
              (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
                (show TensorRSSpace 2 2 I x from
                  TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x))
                (Module.finrank ℝ E) e K J) ^ 2) ≤ C ^ 2 := by
  classical
  obtain ⟨C0, hC0_nn, hC0⟩ :=
    exists_ricEndoRaisedFib_perturbed_gQuadratic_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨2 * (Module.finrank ℝ E : ℝ) * C0, by positivity, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv e horth K
  have hR1 : ∀ v : TangentSpace I x,
      g₀.inner x (ricEndoRaisedFib (I := I) g₁ x v) (ricEndoRaisedFib (I := I) g₁ x v)
        ≤ C0 ^ 2 * g₀.inner x v v :=
    fun v => hC0 g₁ P hδ_le hδ htie x henv v
  have habs0 : ∀ J : Fin 2 → Fin (Module.finrank ℝ E),
      |g₀.inner x (e (K 0)) (ricEndoRaisedFib (I := I) g₁ x (e (J 0)))| ≤ C0 :=
    fun J => ricciArm_component_abs_le (I := I) (M := M) g₀ g₁ x e horth C0 hC0_nn hR1 0 K J
  have habs1 : ∀ J : Fin 2 → Fin (Module.finrank ℝ E),
      |g₀.inner x (e (K 1)) (ricEndoRaisedFib (I := I) g₁ x (e (J 1)))| ≤ C0 :=
    fun J => ricciArm_component_abs_le (I := I) (M := M) g₀ g₁ x e horth C0 hC0_nn hR1 1 K J
  have hterm : ∀ J : Fin 2 → Fin (Module.finrank ℝ E),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x))
        (Module.finrank ℝ E) e K J) ^ 2 ≤
        2 * C0 ^ 2 * (if K 1 = J 1 then (1 : ℝ) else 0)
          + 2 * C0 ^ 2 * (if K 0 = J 0 then (1 : ℝ) else 0) := by
    intro J
    rw [ricciArm_fiberComponent_eq (I := I) (M := M) g₀ g₁ x e horth K J]
    set s0 : ℝ := g₀.inner x (e (K 0)) (ricEndoRaisedFib (I := I) g₁ x (e (J 0))) with hs0
    set s1 : ℝ := g₀.inner x (e (K 1)) (ricEndoRaisedFib (I := I) g₁ x (e (J 1))) with hs1
    have hs0sq : s0 ^ 2 ≤ C0 ^ 2 := by
      have h := habs0 J
      rw [← hs0] at h
      nlinarith [h, abs_nonneg s0, sq_abs s0, neg_le_of_abs_le h, le_of_abs_le h]
    have hs1sq : s1 ^ 2 ≤ C0 ^ 2 := by
      have h := habs1 J
      rw [← hs1] at h
      nlinarith [h, abs_nonneg s1, sq_abs s1, neg_le_of_abs_le h, le_of_abs_le h]
    have hi0 : (if K 1 = J 1 then (1 : ℝ) else 0) = 0 ∨
        (if K 1 = J 1 then (1 : ℝ) else 0) = 1 := by
      by_cases h : K 1 = J 1 <;> simp [h]
    have hi1 : (if K 0 = J 0 then (1 : ℝ) else 0) = 0 ∨
        (if K 0 = J 0 then (1 : ℝ) else 0) = 1 := by
      by_cases h : K 0 = J 0 <;> simp [h]
    rcases hi0 with hi0 | hi0 <;> rcases hi1 with hi1 | hi1 <;>
      rw [hi0, hi1] <;> nlinarith [hs0sq, hs1sq, sq_nonneg (s0 + s1), sq_nonneg s0, sq_nonneg s1,
        sq_nonneg (s0 - s1)]
  calc (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
          (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
            (show TensorRSSpace 2 2 I x from
              TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x))
            (Module.finrank ℝ E) e K J) ^ 2)
      ≤ ∑ J : Fin 2 → Fin (Module.finrank ℝ E),
          (2 * C0 ^ 2 * (if K 1 = J 1 then (1 : ℝ) else 0)
            + 2 * C0 ^ 2 * (if K 0 = J 0 then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum (fun J _ => hterm J)
    _ = 4 * (Module.finrank ℝ E : ℝ) * C0 ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rw [show (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
            (if K 1 = J 1 then (1 : ℝ) else 0)) = (Module.finrank ℝ E : ℝ) from
          slice_indicator_sum_eq_dim K 1]
        rw [show (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
            (if K 0 = J 0 then (1 : ℝ) else 0)) = (Module.finrank ℝ E : ℝ) from
          slice_indicator_sum_eq_dim K 0]
        ring
    _ ≤ (2 * (Module.finrank ℝ E : ℝ) * C0) ^ 2 := by
        have hn1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
          have : 1 ≤ Module.finrank ℝ E := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
          exact_mod_cast this
        have hnn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by positivity
        nlinarith [sq_nonneg C0, hC0_nn, hn1, hnn,
          mul_le_mul_of_nonneg_right hn1 (by positivity : (0:ℝ) ≤ 4 * (Module.finrank ℝ E : ℝ) * C0 ^ 2)]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_ricciArmOrder0CurvCoeffFib_perturbed_riemannianFiberNormSq_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ max δ₀ 0)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              (show TensorRSSpace 2 2 I x from
                TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x)) ≤ C ^ 2 := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_ricciArmOrder0CurvCoeffFib_perturbed_frameComponentSlice_sq_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨(Module.finrank ℝ E : ℝ) * C, by positivity, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv
  have hred := riemannianFiberNormSq_le_of_componentSlice_sq_sum_le (I := I) (M := M) g₀ x
    (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x))
    C hC_nn (fun e horth K => hC g₁ P hδ_le hδ htie x henv e horth K)
  refine le_trans hred (le_of_eq ?_)
  rw [mul_pow]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_riemannBiContrFib_perturbed_frameComponent_sum_sq_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ max δ₀ 0)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
          ∀ (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
            (_horth : ∀ a b : Fin (Module.finrank ℝ E),
              g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
            (K : Fin 2 → Fin (Module.finrank ℝ E)),
            (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
              (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
                (show TensorRSSpace 2 2 I x from
                  TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))
                (Module.finrank ℝ E) e K J) ^ 2) ≤ C ^ 2 := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_riemannBiContrFib_perturbed_riemannianFiberNormSq_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv e horth K
  refine le_trans
    (componentSlice_sq_sum_le_riemannianFiberNormSq (I := I) (M := M) g₀ x
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (riemannBiContrFib (I := I) g₁ x))
      e horth K)
    (hC g₁ P hδ_le hδ htie x henv)

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_ricciArmOrder0CurvCoeffFib_perturbed_frameComponent_sum_sq_le_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ)
    (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ max δ₀ 0)
        (_hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (_htie : ∀ (x : M) (v w : TangentSpace I x),
          g₁.inner x v w = g₀.inner x v w +
            ccTensorBilinSymm (I := I) g₀ P x v w)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
          ∀ (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
            (_horth : ∀ a b : Fin (Module.finrank ℝ E),
              g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0)
            (K : Fin 2 → Fin (Module.finrank ℝ E)),
            (∑ J : Fin 2 → Fin (Module.finrank ℝ E),
              (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
                (show TensorRSSpace 2 2 I x from
                  TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x))
                (Module.finrank ℝ E) e K J) ^ 2) ≤ C ^ 2 := by
  classical
  obtain ⟨C, hC_nn, hC⟩ :=
    exists_ricciArmOrder0CurvCoeffFib_perturbed_riemannianFiberNormSq_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv e horth K
  refine le_trans
    (componentSlice_sq_sum_le_riemannianFiberNormSq (I := I) (M := M) g₀ x
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (ricciArmOrder0CurvCoeffFib (I := I) g₁ x))
      e horth K)
    (hC g₁ P hδ_le hδ htie x henv)

end Curvature
end Geometry
end DifferentialGeometry

end
