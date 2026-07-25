import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformRiemannOperatorNormBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovDerivConnDiffQuadraticBound
import DifferentialGeometry.Geometry.Metric.MetricBounds


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] in
private lemma gNorm_self_triangle
    (g : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x) :
    Real.sqrt (g.inner x (a + b) (a + b)) ≤
      Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) := by
  have haa : 0 ≤ g.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g x a
  have hbb : 0 ≤ g.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g x b
  have hcs : g.inner x a b ≤ Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b) := by
    refine le_trans (le_abs_self _) ?_
    exact abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g x a b
  have hexpand : g.inner x (a + b) (a + b) =
      g.inner x a a + 2 * g.inner x a b + g.inner x b b := by
    have h1 : g.inner x (a + b) (a + b) =
        g.inner x a (a + b) + g.inner x b (a + b) := by
      rw [map_add (g.inner x), ContinuousLinearMap.add_apply]
    have h2 : g.inner x a (a + b) = g.inner x a a + g.inner x a b :=
      map_add (g.inner x a) a b
    have h3 : g.inner x b (a + b) = g.inner x b a + g.inner x b b :=
      map_add (g.inner x b) a b
    have h4 : g.inner x b a = g.inner x a b := g.symm x b a
    rw [h1, h2, h3, h4]; ring
  have hsum_nn : 0 ≤ Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [show Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) =
      Real.sqrt ((Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b)) ^ 2) from
    (Real.sqrt_sq hsum_nn).symm]
  refine Real.sqrt_le_sqrt ?_
  rw [hexpand]
  have hsq : (Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b)) ^ 2 =
      g.inner x a a + 2 * (Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)) +
        g.inner x b b := by
    rw [add_sq, Real.sq_sqrt haa, Real.sq_sqrt hbb]; ring
  rw [hsq]
  linarith [hcs]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] in
private lemma gNorm_self_sub_triangle
    (g : SmoothRiemannianMetric I M) (x : M) (a b : TangentSpace I x) :
    Real.sqrt (g.inner x (a - b) (a - b)) ≤
      Real.sqrt (g.inner x a a) + Real.sqrt (g.inner x b b) := by
  have h := gNorm_self_triangle (I := I) (M := M) g x a (-b)
  have hnb : g.inner x (-b) (-b) = g.inner x b b := by
    rw [map_neg (g.inner x), ContinuousLinearMap.neg_apply, map_neg, neg_neg]
  rw [hnb] at h
  rw [show a - b = a + (-b) from by abel]
  exact h

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_riemannOp_LeviCivita_difference_gQuadratic_le_of_jetEnvelope
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
          ∀ v w u : TangentSpace I x,
            g₀.inner x
                (riemannOp (cov := LeviCivita (I := I) g₁) x v w u -
                  riemannOp (cov := LeviCivita (I := I) g₀) x v w u)
                (riemannOp (cov := LeviCivita (I := I) g₁) x v w u -
                  riemannOp (cov := LeviCivita (I := I) g₀) x v w u) ≤
              C ^ 2 * g₀.inner x v v * g₀.inner x w w * g₀.inner x u u := by
  classical
  set m : ℝ := max δ₀ 0 with hm_def
  have hm0 : 0 ≤ m := le_max_right _ _
  have hm1 : m < 1 := max_lt hδ₀ (by norm_num)
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope (I := I) (M := M) g₀ hδ₀ B hB
  obtain ⟨C0, hC0_nn, hC0⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hm0 hm1
  refine ⟨2 * CA + 2 * (C0 ^ 2 * B ^ 2), by positivity, ?_⟩
  intro g₁ P δ hδ_le hδ htie x henv v w u
  set X : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hX_def
  set Y : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x w with hY_def
  set Z : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x u with hZ_def
  have hX_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) := smoothExtensionTangent_contMDiff x v
  have hY_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y) := smoothExtensionTangent_contMDiff x w
  have hZ_sm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Z) := smoothExtensionTangent_contMDiff x u
  have hXx : X x = v := smoothExtensionTangent_eq x v
  have hYx : Y x = w := smoothExtensionTangent_eq x w
  have hZx : Z x = u := smoothExtensionTangent_eq x u
  set R1 : TangentSpace I x := riemannOp (cov := LeviCivita (I := I) g₁) x v w u with hR1_def
  set R0 : TangentSpace I x := riemannOp (cov := LeviCivita (I := I) g₀) x v w u with hR0_def
  have hR1_sec : R1 = riemannSec (LeviCivita (I := I) g₁) X Y Z x := by
    rw [hR1_def, ← hXx, ← hYx, ← hZx,
      riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁) hX_sm hY_sm hZ_sm]
  have hR0_sec : R0 = riemannSec (LeviCivita (I := I) g₀) X Y Z x := by
    rw [hR0_def, ← hXx, ← hYx, ← hZx,
      riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀) hX_sm hY_sm hZ_sm]
  have htor : (LeviCivita (I := I) g₀).torsion = 0 := LeviCivita_torsion_eq_zero (I := I) g₀
  have hdiff := riemannSec_difference (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
    hX_sm hY_sm hZ_sm htor x
  set A1 : TangentSpace I x :=
    covDerivConnDiff (I := I) g₀ g₁ X Y Z x with hA1_def
  set A2 : TangentSpace I x :=
    covDerivConnDiff (I := I) g₀ g₁ Y X Z x with hA2_def
  set S1 : TangentSpace I x :=
    diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) Y Z x with hS1_def
  set S2 : TangentSpace I x :=
    diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) X Z x with hS2_def
  set Q1 : TangentSpace I x :=
    CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x S1 (X x)
    with hQ1_def
  set Q2 : TangentSpace I x :=
    CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x S2 (Y x)
    with hQ2_def
  have hRsub : R1 - R0 = (A1 - A2) + (Q1 - Q2) := by
    rw [hR1_sec, hR0_sec, hdiff]
    rw [show covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) X Y Z x = A1 from rfl,
      show covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁) Y X Z x = A2 from rfl]
    abel
  letI instTens3 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  set Np : ℝ :=
    (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + 1) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
    ‖(iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x‖) with hNp_def
  have hNp_nn : 0 ≤ Np := by rw [hNp_def]; exact norm_nonneg _
  have hNp_le_B : Np ≤ B := by
    have hsum_terms : ∀ j ∈ Finset.range 3, (0 : ℝ) ≤
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
        ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖) := by
      intro j _
      letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + j) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
      exact norm_nonneg ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)
    have h1mem : (1 : ℕ) ∈ Finset.range 3 := by decide
    exact le_trans (Finset.single_le_sum hsum_terms h1mem) henv

  have hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) (max δ 0) := by
    intro y a b
    refine le_trans (hδ y a b) ?_
    have hle : δ ≤ max δ 0 := le_max_left _ _
    have hnn : 0 ≤ Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc δ * Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)
        = δ * (Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)) := by ring
      _ ≤ max δ 0 * (Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)) :=
          mul_le_mul_of_nonneg_right hle hnn
      _ = max δ 0 * Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) := by ring
  have hδ'_le : max δ 0 ≤ m := max_le hδ_le hm0
  have hδ'_nn : 0 ≤ max δ 0 := le_max_right _ _

  have hconn0 : ∀ a b : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b)
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x a b)) ≤
        C0 * Np * Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) := by
    intro a b
    have h := hC0 g₁ P htie hδ'_le hδ'_nn hδ' x a b
    rw [← hNp_def] at h
    exact h
  have hg0vv_nn : 0 ≤ g₀.inner x v v := metric_inner_self_nonneg (I := I) (M := M) g₀ x v
  have hg0ww_nn : 0 ≤ g₀.inner x w w := metric_inner_self_nonneg (I := I) (M := M) g₀ x w
  have hg0uu_nn : 0 ≤ g₀.inner x u u := metric_inner_self_nonneg (I := I) (M := M) g₀ x u
  set Sv : ℝ := Real.sqrt (g₀.inner x v v) with hSv_def
  set Sw : ℝ := Real.sqrt (g₀.inner x w w) with hSw_def
  set Su : ℝ := Real.sqrt (g₀.inner x u u) with hSu_def
  have hSv_nn : 0 ≤ Sv := Real.sqrt_nonneg _
  have hSw_nn : 0 ≤ Sw := Real.sqrt_nonneg _
  have hSu_nn : 0 ≤ Su := Real.sqrt_nonneg _

  have hA1_bd : Real.sqrt (g₀.inner x A1 A1) ≤ CA * Sv * Sw * Su := by
    have h := hCA g₁ P hδ_le hδ htie x henv v w u
    rw [← hX_def, ← hY_def, ← hZ_def, ← hSv_def, ← hSw_def, ← hSu_def] at h
    rw [hA1_def]
    exact h
  have hA2_bd : Real.sqrt (g₀.inner x A2 A2) ≤ CA * Sw * Sv * Su := by
    have h := hCA g₁ P hδ_le hδ htie x henv w v u
    rw [← hX_def, ← hY_def, ← hZ_def, ← hSv_def, ← hSw_def, ← hSu_def] at h
    rw [hA2_def]
    exact h

  have hS1_eq : S1 = PDE.DeTurck.connDiff (I := I) g₁ g₀ x u w := by
    rw [hS1_def]
    change CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
        (Z x) (Y x) = _
    rw [hZx, hYx, ← connDiff_eq_difference (I := I) g₀ g₁]
  have hS2_eq : S2 = PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v := by
    rw [hS2_def]
    change CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
        (Z x) (X x) = _
    rw [hZx, hXx, ← connDiff_eq_difference (I := I) g₀ g₁]
  have hQ1_eq : Q1 = PDE.DeTurck.connDiff (I := I) g₁ g₀ x S1 v := by
    rw [hQ1_def, ← connDiff_eq_difference (I := I) g₀ g₁, hXx]
  have hQ2_eq : Q2 = PDE.DeTurck.connDiff (I := I) g₁ g₀ x S2 w := by
    rw [hQ2_def, ← connDiff_eq_difference (I := I) g₀ g₁, hYx]

  have hQ1_bd : Real.sqrt (g₀.inner x Q1 Q1) ≤ (C0 ^ 2 * B ^ 2) * Sv * Sw * Su := by
    rw [hQ1_eq]
    have hS1_bd : Real.sqrt (g₀.inner x S1 S1) ≤ C0 * Np * Su * Sw := by
      rw [hS1_eq]
      have := hconn0 u w
      rw [← hSu_def, ← hSw_def] at this
      exact this
    have hQ1' := hconn0 S1 v
    rw [← hSv_def] at hQ1'
    have hS1_norm_nn : 0 ≤ Real.sqrt (g₀.inner x S1 S1) := Real.sqrt_nonneg _
    have hC0Np_nn : 0 ≤ C0 * Np := mul_nonneg hC0_nn hNp_nn
    calc Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x S1 v)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x S1 v))
        ≤ C0 * Np * Real.sqrt (g₀.inner x S1 S1) * Sv := hQ1'
      _ ≤ C0 * Np * (C0 * Np * Su * Sw) * Sv := by
          have hmono : C0 * Np * Real.sqrt (g₀.inner x S1 S1) ≤ C0 * Np * (C0 * Np * Su * Sw) :=
            mul_le_mul_of_nonneg_left hS1_bd hC0Np_nn
          exact mul_le_mul_of_nonneg_right hmono hSv_nn
      _ = (C0 ^ 2 * Np ^ 2) * Sv * Sw * Su := by ring
      _ ≤ (C0 ^ 2 * B ^ 2) * Sv * Sw * Su := by
          have hNpB : Np ^ 2 ≤ B ^ 2 := by
            have := hNp_le_B
            nlinarith [hNp_nn, hB, this]
          have hfac : C0 ^ 2 * Np ^ 2 ≤ C0 ^ 2 * B ^ 2 :=
            mul_le_mul_of_nonneg_left hNpB (sq_nonneg _)
          have hprod_nn : 0 ≤ Sv * Sw * Su :=
            mul_nonneg (mul_nonneg hSv_nn hSw_nn) hSu_nn
          have hstep : (C0 ^ 2 * Np ^ 2) * (Sv * Sw * Su) ≤
              (C0 ^ 2 * B ^ 2) * (Sv * Sw * Su) :=
            mul_le_mul_of_nonneg_right hfac hprod_nn
          calc (C0 ^ 2 * Np ^ 2) * Sv * Sw * Su
              = (C0 ^ 2 * Np ^ 2) * (Sv * Sw * Su) := by ring
            _ ≤ (C0 ^ 2 * B ^ 2) * (Sv * Sw * Su) := hstep
            _ = (C0 ^ 2 * B ^ 2) * Sv * Sw * Su := by ring
  have hQ2_bd : Real.sqrt (g₀.inner x Q2 Q2) ≤ (C0 ^ 2 * B ^ 2) * Sv * Sw * Su := by
    rw [hQ2_eq]
    have hS2_bd : Real.sqrt (g₀.inner x S2 S2) ≤ C0 * Np * Su * Sv := by
      rw [hS2_eq]
      have := hconn0 u v
      rw [← hSu_def, ← hSv_def] at this
      exact this
    have hQ2' := hconn0 S2 w
    rw [← hSw_def] at hQ2'
    have hC0Np_nn : 0 ≤ C0 * Np := mul_nonneg hC0_nn hNp_nn
    calc Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x S2 w)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x S2 w))
        ≤ C0 * Np * Real.sqrt (g₀.inner x S2 S2) * Sw := hQ2'
      _ ≤ C0 * Np * (C0 * Np * Su * Sv) * Sw := by
          have hmono : C0 * Np * Real.sqrt (g₀.inner x S2 S2) ≤ C0 * Np * (C0 * Np * Su * Sv) :=
            mul_le_mul_of_nonneg_left hS2_bd hC0Np_nn
          exact mul_le_mul_of_nonneg_right hmono hSw_nn
      _ = (C0 ^ 2 * Np ^ 2) * Sv * Sw * Su := by ring
      _ ≤ (C0 ^ 2 * B ^ 2) * Sv * Sw * Su := by
          have hNpB : Np ^ 2 ≤ B ^ 2 := by
            have := hNp_le_B
            nlinarith [hNp_nn, hB, this]
          have hfac : C0 ^ 2 * Np ^ 2 ≤ C0 ^ 2 * B ^ 2 :=
            mul_le_mul_of_nonneg_left hNpB (sq_nonneg _)
          have hprod_nn : 0 ≤ Sv * Sw * Su :=
            mul_nonneg (mul_nonneg hSv_nn hSw_nn) hSu_nn
          have hstep : (C0 ^ 2 * Np ^ 2) * (Sv * Sw * Su) ≤
              (C0 ^ 2 * B ^ 2) * (Sv * Sw * Su) :=
            mul_le_mul_of_nonneg_right hfac hprod_nn
          calc (C0 ^ 2 * Np ^ 2) * Sv * Sw * Su
              = (C0 ^ 2 * Np ^ 2) * (Sv * Sw * Su) := by ring
            _ ≤ (C0 ^ 2 * B ^ 2) * (Sv * Sw * Su) := hstep
            _ = (C0 ^ 2 * B ^ 2) * Sv * Sw * Su := by ring

  set Kc : ℝ := 2 * CA + 2 * (C0 ^ 2 * B ^ 2) with hKc_def
  have hKc_nn : 0 ≤ Kc := by rw [hKc_def]; positivity
  have hRsub_bd : Real.sqrt (g₀.inner x (R1 - R0) (R1 - R0)) ≤ Kc * Sv * Sw * Su := by
    rw [hRsub]
    have hA1_norm := hA1_bd
    have hA2_norm : Real.sqrt (g₀.inner x A2 A2) ≤ CA * Sv * Sw * Su := by
      calc Real.sqrt (g₀.inner x A2 A2) ≤ CA * Sw * Sv * Su := hA2_bd
        _ = CA * Sv * Sw * Su := by ring
    have htri1 : Real.sqrt (g₀.inner x (A1 - A2) (A1 - A2)) ≤
        CA * Sv * Sw * Su + CA * Sv * Sw * Su :=
      le_trans (gNorm_self_sub_triangle (I := I) (M := M) g₀ x A1 A2)
        (add_le_add hA1_norm hA2_norm)
    have htri2 : Real.sqrt (g₀.inner x (Q1 - Q2) (Q1 - Q2)) ≤
        (C0 ^ 2 * B ^ 2) * Sv * Sw * Su + (C0 ^ 2 * B ^ 2) * Sv * Sw * Su :=
      le_trans (gNorm_self_sub_triangle (I := I) (M := M) g₀ x Q1 Q2)
        (add_le_add hQ1_bd hQ2_bd)
    have htri := gNorm_self_triangle (I := I) (M := M) g₀ x (A1 - A2) (Q1 - Q2)
    calc Real.sqrt (g₀.inner x ((A1 - A2) + (Q1 - Q2)) ((A1 - A2) + (Q1 - Q2)))
        ≤ Real.sqrt (g₀.inner x (A1 - A2) (A1 - A2)) +
            Real.sqrt (g₀.inner x (Q1 - Q2) (Q1 - Q2)) := htri
      _ ≤ (CA * Sv * Sw * Su + CA * Sv * Sw * Su) +
            ((C0 ^ 2 * B ^ 2) * Sv * Sw * Su + (C0 ^ 2 * B ^ 2) * Sv * Sw * Su) :=
          add_le_add htri1 htri2
      _ = Kc * Sv * Sw * Su := by rw [hKc_def]; ring

  have hRsub_nn : 0 ≤ g₀.inner x (R1 - R0) (R1 - R0) :=
    metric_inner_self_nonneg (I := I) (M := M) g₀ x (R1 - R0)
  have hrhs_nn : 0 ≤ Kc * Sv * Sw * Su :=
    mul_nonneg (mul_nonneg (mul_nonneg hKc_nn hSv_nn) hSw_nn) hSu_nn
  have hsq : g₀.inner x (R1 - R0) (R1 - R0) ≤ (Kc * Sv * Sw * Su) ^ 2 := by
    have hmul := mul_le_mul hRsub_bd hRsub_bd (Real.sqrt_nonneg _) hrhs_nn
    rw [Real.mul_self_sqrt hRsub_nn] at hmul
    rw [sq]; exact hmul
  calc g₀.inner x (R1 - R0) (R1 - R0) ≤ (Kc * Sv * Sw * Su) ^ 2 := hsq
    _ = Kc ^ 2 * (Sv ^ 2) * (Sw ^ 2) * (Su ^ 2) := by ring
    _ = Kc ^ 2 * g₀.inner x v v * g₀.inner x w w * g₀.inner x u u := by
        rw [hSv_def, hSw_def, hSu_def, Real.sq_sqrt hg0vv_nn, Real.sq_sqrt hg0ww_nn,
          Real.sq_sqrt hg0uu_nn]

end Curvature
end Geometry
end DifferentialGeometry

end
