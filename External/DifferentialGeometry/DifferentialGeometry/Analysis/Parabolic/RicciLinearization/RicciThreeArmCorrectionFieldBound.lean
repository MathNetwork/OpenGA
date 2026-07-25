import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RealizedFamCurvatureJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PerturbedRiemannOpDifferenceBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovDerivConnDiffQuadraticBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def gInvDiffQuadResidualFieldRealizedFam (g₀ : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) : SmoothCcTensor g₀ 2 2 :=
  connDiffBiContrCoeffField (I := I) (M := M)
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_connDiffBiContrFib_self
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x)
    (K J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) g₁ g₀ g₁ g₀ x)) n e K J =
      ∑ aa : Fin (Module.finrank ℝ E), ∑ bb : Fin (Module.finrank ℝ E),
        g₀.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (smoothOrthoFrame (I := I) g₀ x aa x)
                (smoothOrthoFrame (I := I) g₀ x bb x))
              (e (J 0)))
            (e (J 1)) *
          (g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₀ x aa x) *
            g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₀ x bb x)) := by
  classical
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) g₁ g₀ g₁ g₀ x)) n e K J =
      Tensor0SSpace.toModel
        ((connDiffBiContrFib (I := I) g₁ g₀ g₁ g₀ x)
          (coframeS (I := I) (M := M) g₀ x 2 e K))
        (fun i => (e (J i) : E)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hcomp]
  rw [show (connDiffBiContrFib (I := I) g₁ g₀ g₁ g₀ x) =
      connDiffBiContrFibFixedFrame (I := I) g₁ g₀ g₁ g₀ (smoothOrthoFrame (I := I) g₀ x) x from rfl]
  rw [connDiffBiContrFibFixedFrame_toModel]
  refine Finset.sum_congr rfl (fun aa _ => Finset.sum_congr rfl (fun bb _ => ?_))
  have hcf : (coframeS (I := I) (M := M) g₀ x 2 e K).toModel
        ![(smoothOrthoFrame (I := I) g₀ x aa x : E), (smoothOrthoFrame (I := I) g₀ x bb x : E)]
      = g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₀ x aa x) *
          g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₀ x bb x) := by
    rw [show (coframeS (I := I) (M := M) g₀ x 2 e K).toModel
          ![(smoothOrthoFrame (I := I) g₀ x aa x : E), (smoothOrthoFrame (I := I) g₀ x bb x : E)]
        = coframeS (I := I) (M := M) g₀ x 2 e K
          ![smoothOrthoFrame (I := I) g₀ x aa x, smoothOrthoFrame (I := I) g₀ x bb x] from rfl]
    rw [coframeS_apply, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hcf]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem riemannianFiberNormSq_gInvDiffQuadResidualField_le_of_lt_one
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (P : SmoothCcTensor g₀ 0 2)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
      {δ : ℝ} (_hδ : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
      (x : M),
      letI : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) g₁ g₀ g₁ g₀ x)) ≤
        C * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 4 := by
  classical
  letI instTens : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨C₀, hC₀0, hpw⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδ₀0 hδ₀
  refine ⟨((Module.finrank ℝ E : ℝ) ^ 4 * C₀ ^ 2) ^ 2, by positivity, ?_⟩
  intro g₁ P h δ hδ hδ0 hbound x
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum_rfns⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  have hsofnn : ∀ aa : Fin (Module.finrank ℝ E),
      g₀.inner x (smoothOrthoFrame (I := I) g₀ x aa x) (smoothOrthoFrame (I := I) g₀ x aa x) = 1 := by
    intro aa; rw [smoothOrthoFrame_orthonormal_at_center]; simp
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 2 2 x
    (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) g₁ g₀ g₁ g₀ x))
    e bse hnE hbse horth]
  have heach : ∀ (K J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) g₁ g₀ g₁ g₀ x)) n e K J) ^ 2 ≤
        ((Module.finrank ℝ E : ℝ) ^ 2 * C₀ ^ 2 * G ^ 2) ^ 2 := by
    intro K J
    rw [fiberNormSqComponent_connDiffBiContrFib_self (I := I) g₀ g₁ x e K J]
    have hJ0 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
    have hJ1 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by rw [horth (J 1) (J 1)]; simp
    have hK0 : g₀.inner x (e (K 0)) (e (K 0)) = 1 := by rw [horth (K 0) (K 0)]; simp
    have hK1 : g₀.inner x (e (K 1)) (e (K 1)) = 1 := by rw [horth (K 1) (K 1)]; simp
    have hterm : ∀ aa bb : Fin (Module.finrank ℝ E),
        |g₀.inner x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (smoothOrthoFrame (I := I) g₀ x aa x)
                (smoothOrthoFrame (I := I) g₀ x bb x))
              (e (J 0)))
            (e (J 1)) *
          (g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₀ x aa x) *
            g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₀ x bb x))| ≤ C₀ ^ 2 * G ^ 2 := by
      intro aa bb
      set Wab : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (smoothOrthoFrame (I := I) g₀ x aa x) (smoothOrthoFrame (I := I) g₀ x bb x) with hWab
      set Uab : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x Wab (e (J 0)) with hUab
      have hWab_le : Real.sqrt (g₀.inner x Wab Wab) ≤ C₀ * G := by
        have hh := hpw g₁ P h hδ hδ0 hbound x
          (smoothOrthoFrame (I := I) g₀ x aa x) (smoothOrthoFrame (I := I) g₀ x bb x)
        rw [← hWab, hsofnn aa, hsofnn bb, Real.sqrt_one, mul_one, mul_one, ← hG_def] at hh
        exact hh
      have hUab_le : Real.sqrt (g₀.inner x Uab Uab) ≤ C₀ * G * (C₀ * G) := by
        have hh := hpw g₁ P h hδ hδ0 hbound x Wab (e (J 0))
        rw [← hUab, hJ0, Real.sqrt_one, mul_one, ← hG_def] at hh
        exact le_trans hh (mul_le_mul_of_nonneg_left hWab_le (by positivity))
      have hfirst : |g₀.inner x Uab (e (J 1))| ≤ C₀ ^ 2 * G ^ 2 := by
        have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x Uab (e (J 1))
        rw [hJ1, Real.sqrt_one, mul_one] at hcs
        exact le_trans hcs (le_trans hUab_le (le_of_eq (by ring)))
      have hcross1 : |g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₀ x aa x)| ≤ 1 := by
        have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x
          (e (K 0)) (smoothOrthoFrame (I := I) g₀ x aa x)
        rw [hK0, hsofnn aa, Real.sqrt_one, mul_one] at hcs
        exact hcs
      have hcross2 : |g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₀ x bb x)| ≤ 1 := by
        have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x
          (e (K 1)) (smoothOrthoFrame (I := I) g₀ x bb x)
        rw [hK1, hsofnn bb, Real.sqrt_one, mul_one] at hcs
        exact hcs
      rw [abs_mul, abs_mul]
      have hC₀G_nn : 0 ≤ C₀ ^ 2 * G ^ 2 := by positivity
      calc |g₀.inner x Uab (e (J 1))| *
              (|g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₀ x aa x)| *
                |g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₀ x bb x)|)
          ≤ (C₀ ^ 2 * G ^ 2) * (1 * 1) :=
            mul_le_mul hfirst
              (mul_le_mul hcross1 hcross2 (abs_nonneg _) (by norm_num))
              (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hC₀G_nn
        _ = C₀ ^ 2 * G ^ 2 := by ring
    have habs : |∑ aa : Fin (Module.finrank ℝ E), ∑ bb : Fin (Module.finrank ℝ E),
          g₀.inner x
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (smoothOrthoFrame (I := I) g₀ x aa x)
                  (smoothOrthoFrame (I := I) g₀ x bb x))
                (e (J 0)))
              (e (J 1)) *
            (g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₀ x aa x) *
              g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₀ x bb x))| ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * C₀ ^ 2 * G ^ 2 := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun aa _ => Finset.abs_sum_le_sum_abs _ _)) ?_
      refine le_trans (Finset.sum_le_sum (fun aa _ =>
        Finset.sum_le_sum (fun bb _ => hterm aa bb))) ?_
      have hconst : (∑ _aa : Fin (Module.finrank ℝ E), ∑ _bb : Fin (Module.finrank ℝ E),
            C₀ ^ 2 * G ^ 2) = (Module.finrank ℝ E : ℝ) ^ 2 * C₀ ^ 2 * G ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      rw [hconst]
    calc (∑ aa : Fin (Module.finrank ℝ E), ∑ bb : Fin (Module.finrank ℝ E),
            g₀.inner x
                (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                  (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                    (smoothOrthoFrame (I := I) g₀ x aa x)
                    (smoothOrthoFrame (I := I) g₀ x bb x))
                  (e (J 0)))
                (e (J 1)) *
              (g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₀ x aa x) *
                g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₀ x bb x))) ^ 2
        = |∑ aa : Fin (Module.finrank ℝ E), ∑ bb : Fin (Module.finrank ℝ E),
              g₀.inner x
                  (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                    (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
                      (smoothOrthoFrame (I := I) g₀ x aa x)
                      (smoothOrthoFrame (I := I) g₀ x bb x))
                    (e (J 0)))
                  (e (J 1)) *
                (g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₀ x aa x) *
                  g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₀ x bb x))| ^ 2 :=
          (sq_abs _).symm
      _ ≤ ((Module.finrank ℝ E : ℝ) ^ 2 * C₀ ^ 2 * G ^ 2) ^ 2 := by gcongr
  calc ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (connDiffBiContrFib (I := I) g₁ g₀ g₁ g₀ x)) n e K J) ^ 2
      ≤ ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
          ((Module.finrank ℝ E : ℝ) ^ 2 * C₀ ^ 2 * G ^ 2) ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 2 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ) *
          (((Module.finrank ℝ E : ℝ) ^ 2 * C₀ ^ 2 * G ^ 2) ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = ((Module.finrank ℝ E : ℝ) ^ 4 * C₀ ^ 2) ^ 2 * G ^ 4 := by
        have hcard : (Fintype.card (Fin 2 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ)
            = (n : ℝ) ^ 4 := by
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
          push_cast; ring
        rw [hcard, ← hnE]; ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_gInvDiffQuadResidualField_realizedFam_riemannianFiberNormSq_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((gInvDiffQuadResidualFieldRealizedFam (I := I) g₀ T T' hδ hδ' s).toSection x) ≤ Λ := by
  classical
  obtain ⟨C, hC0, hbnd⟩ :=
    riemannianFiberNormSq_gInvDiffQuadResidualField_le_of_lt_one (I := I) (M := M) g₀
      (le_max_right δ₀ 0) (max_lt hδ₀ (by norm_num))
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) (M := M) g₀ a ha_super
  refine ⟨C * (Csob * R) ^ 4, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  letI instTens : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  set m : ℝ := max δ₀ 0 with hm_def
  have hm0 : 0 ≤ m := le_max_right _ _
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs_mem y v w
  have hδs_raw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  obtain ⟨hs0, hs1⟩ := hs
  have habs_eq : |1 - s| * δ' + |s| * δ = (1 - s) * δ' + s * δ := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
  have hsmall_le : (1 - s) * δ' + s * δ ≤ m := by
    have h1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le (by linarith)
    have h2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have hδ₀_le : δ₀ ≤ m := le_max_left _ _
    nlinarith [h1, h2, hδ₀_le]
  have hδs : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)) m := by
    intro y v w
    refine le_trans (hδs_raw y v w) ?_
    have hprod : 0 ≤ Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hle' : |1 - s| * δ' + |s| * δ ≤ m := by rw [habs_eq]; exact hsmall_le
    nlinarith [hle', hprod]
  have hmain := hbnd (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) htie (le_of_eq hm_def.symm) hm0 hδs x
  rw [show (gInvDiffQuadResidualFieldRealizedFam (I := I) g₀ T T' hδ hδ' s).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffBiContrFib (I := I)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g₀ x)) from rfl]
  refine le_trans hmain ?_
  have hG_le : ‖((iteratedCovGrad (I := I) g₀ 0 2 1
        (convexPerturbation (I := I) g₀ T T' s)).toSection x :
        Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ≤ Csob * R := by
    have hCsob_sum := hCsob T T' hR hTball hT'ball s ⟨hs0, hs1⟩ x
    have hterms : ∀ k ∈ Finset.range 3, 0 ≤
        (letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
        ‖(iteratedCovGrad (I := I) g₀ 0 2 k
            (convexPerturbation (I := I) g₀ T T' s)).toSection x‖) := by
      intro k _
      letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
      exact norm_nonneg _
    exact le_trans (Finset.single_le_sum hterms
      (show (1 : ℕ) ∈ Finset.range 3 from Finset.mem_range.mpr (by norm_num))) hCsob_sum
  gcongr

section NormedBackgroundRiemannCoefficientField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def backgroundRiemannKernelBilin (g₀ : SmoothRiemannianMetric I M) (x : M)
    (p : TangentSpace I x) (D : Tensor0SSpace 2 I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x) ℝ
      (((bilinFormToModel (TangentSpace I x)).symm (Tensor0SSpace.toModel D)).flip p)).comp
    (riemannOp (LeviCivita (I := I) g₀) x p)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem backgroundRiemannKernelBilin_apply (g₀ : SmoothRiemannianMetric I M) (x : M)
    (p : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v0 v1 : TangentSpace I x) :
    backgroundRiemannKernelBilin (I := I) g₀ x p D v0 v1 =
      Tensor0SSpace.toModel D
        ![riemannOp (LeviCivita (I := I) g₀) x p v0 v1, p] := by
  rw [backgroundRiemannKernelBilin, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  exact bilinFormToModel_symm_apply (TangentSpace I x) (Tensor0SSpace.toModel D)
    (riemannOp (LeviCivita (I := I) g₀) x p v0 v1) p

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem backgroundRiemannKernelBilin_add_right (g₀ : SmoothRiemannianMetric I M) (x : M)
    (p : TangentSpace I x) (D D' : Tensor0SSpace 2 I x) :
    backgroundRiemannKernelBilin (I := I) g₀ x p (D + D') =
      backgroundRiemannKernelBilin (I := I) g₀ x p D + backgroundRiemannKernelBilin (I := I) g₀ x p D' := by
  apply ContinuousLinearMap.ext; intro v0
  apply ContinuousLinearMap.ext; intro v1
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, backgroundRiemannKernelBilin_apply,
    backgroundRiemannKernelBilin_apply, backgroundRiemannKernelBilin_apply, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.add_apply]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem backgroundRiemannKernelBilin_smul_right (g₀ : SmoothRiemannianMetric I M) (x : M)
    (p : TangentSpace I x) (c : ℝ) (D : Tensor0SSpace 2 I x) :
    backgroundRiemannKernelBilin (I := I) g₀ x p (c • D) = c • backgroundRiemannKernelBilin (I := I) g₀ x p D := by
  apply ContinuousLinearMap.ext; intro v0
  apply ContinuousLinearMap.ext; intro v1
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, backgroundRiemannKernelBilin_apply,
    backgroundRiemannKernelBilin_apply, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    smul_eq_mul]

def backgroundRiemannSummandFib (g₀ : SmoothRiemannianMetric I M) (x : M) (p : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel E (backgroundRiemannKernelBilin (I := I) g₀ x p D))
      map_add' := fun D D' => by
        apply Tensor0SSpace.toModel_injective
        apply ContinuousMultilinearMap.ext
        intro v
        beta_reduce
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
          Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_ofModel,
          Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply, bilinFormToModel_apply,
          bilinFormToModel_apply, backgroundRiemannKernelBilin_add_right]
        rfl
      map_smul' := fun c D => by
        apply Tensor0SSpace.toModel_injective
        apply ContinuousMultilinearMap.ext
        intro v
        beta_reduce
        rw [RingHom.id_apply, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
          Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply,
          bilinFormToModel_apply, backgroundRiemannKernelBilin_smul_right]
        rfl }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem backgroundRiemannSummandFib_toModel (g₀ : SmoothRiemannianMetric I M) (x : M)
    (p : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (backgroundRiemannSummandFib (I := I) g₀ x p D) v =
      Tensor0SSpace.toModel D
        ![riemannOp (LeviCivita (I := I) g₀) x p (v 0) (v 1), p] := by
  rw [backgroundRiemannSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply]
  exact backgroundRiemannKernelBilin_apply (I := I) g₀ x p D (v 0) (v 1)

def backgroundRiemannBiContrFibFixedFrame (g₀ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  ∑ c : Fin (Module.finrank ℝ E), backgroundRiemannSummandFib (I := I) g₀ x (B c x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem backgroundRiemannBiContrFibFixedFrame_toModel (g₀ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (backgroundRiemannBiContrFibFixedFrame (I := I) g₀ B x D) v =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![riemannOp (LeviCivita (I := I) g₀) x (B c x) (v 0) (v 1), B c x] := by
  classical
  rw [backgroundRiemannBiContrFibFixedFrame, ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, backgroundRiemannSummandFib_toModel]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem backgroundRiemannKernelBilin_homSection_contMDiff (g₀ : SmoothRiemannianMetric I M)
    {p : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (backgroundRiemannKernelBilin (I := I) g₀ x (p x) (Y x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => backgroundRiemannKernelBilin (I := I) g₀ x (p x) (Y x))
  intro V0
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => backgroundRiemannKernelBilin (I := I) g₀ x (p x) (Y x) (V0 x))
  intro W
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) g₀) p V0 W b)) :=
    riemannSec_contMDiff (cov := LeviCivita (I := I) g₀) hp V0.contMDiff W.contMDiff
  have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => Tensor0SSpace.toModel (Y x)
        ![(riemannSec (LeviCivita (I := I) g₀) p V0 W x : E), (p x : E)]) := by
    have h := TensorMultilinear.contMDiff_section_apply (n := 2)
      (fun b => Y b) Y.contMDiff
      (![fun z => riemannSec (LeviCivita (I := I) g₀) p V0 W z, fun z => p z])
      (by
        intro i
        fin_cases i
        · exact hRsec
        · exact hp)
    refine h.congr ?_
    intro x
    congr 1
    funext i
    fin_cases i <;> rfl
  intro x
  rw [contMDiffAt_section]
  refine (hscalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change backgroundRiemannKernelBilin (I := I) g₀ y (p y) (Y y) (V0 y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [backgroundRiemannKernelBilin_apply,
    riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀) hp V0.contMDiff W.contMDiff]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem backgroundRiemannBiContrFibFixedFrame_apply_section_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (backgroundRiemannBiContrFibFixedFrame (I := I) g₀ B x (Y x))) := by
  classical
  have hsummand : ∀ c : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (backgroundRiemannSummandFib (I := I) g₀ x (B c x) (Y x))) := by
    intro c
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => backgroundRiemannKernelBilin (I := I) g₀ x (B c x) (Y x))
      (backgroundRiemannKernelBilin_homSection_contMDiff (I := I) g₀ (hB c) Y)
    refine hbilin.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun c =>
      { toFun := fun x : M => backgroundRiemannSummandFib (I := I) g₀ x (B c x) (Y x)
        contMDiff_toFun := hsummand c } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    ∑ c : Fin (Module.finrank ℝ E), S c with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [backgroundRiemannBiContrFibFixedFrame, hStot_def]
  have hcoe : ((∑ c : Fin (Module.finrank ℝ E), S c :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ c : Fin (Module.finrank ℝ E), ((S c : Π z : M, Tensor0SSpace 2 I z)) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun c => S c) Finset.univ
  have hsum : ((∑ c : Fin (Module.finrank ℝ E), S c :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ c : Fin (Module.finrank ℝ E), (S c : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoe, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.sum_apply]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem backgroundRiemannBiContrFibFixedFrame_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (backgroundRiemannBiContrFibFixedFrame (I := I) g₀ B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => backgroundRiemannBiContrFibFixedFrame (I := I) g₀ B x)
  intro Y
  exact backgroundRiemannBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₀ B hB Y

def backgroundRiemannTraceKernel (g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p =>
        ((bilinFormToModel (TangentSpace I x)).symm (Tensor0SSpace.toModel D))
          (riemannOp (LeviCivita (I := I) g₀) x p v0 v1)
      map_add' := fun p p' => by
        have hr : riemannOp (LeviCivita (I := I) g₀) x (p + p') v0 v1 =
            riemannOp (LeviCivita (I := I) g₀) x p v0 v1 +
              riemannOp (LeviCivita (I := I) g₀) x p' v0 v1 := by
          rw [(riemannOp (LeviCivita (I := I) g₀) x).map_add p p',
            ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
        rw [hr, map_add]
      map_smul' := fun c p => by
        have hr : riemannOp (LeviCivita (I := I) g₀) x (c • p) v0 v1 =
            c • riemannOp (LeviCivita (I := I) g₀) x p v0 v1 := by
          rw [(riemannOp (LeviCivita (I := I) g₀) x).map_smul c p,
            ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
        rw [hr, map_smul, RingHom.id_apply] }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem backgroundRiemannTraceKernel_apply (g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v0 v1 p q : TangentSpace I x) :
    backgroundRiemannTraceKernel (I := I) g₀ x D v0 v1 p q =
      Tensor0SSpace.toModel D
        ![riemannOp (LeviCivita (I := I) g₀) x p v0 v1, q] := by
  rw [backgroundRiemannTraceKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  exact bilinFormToModel_symm_apply (TangentSpace I x) (Tensor0SSpace.toModel D)
    (riemannOp (LeviCivita (I := I) g₀) x p v0 v1) q

def backgroundRiemannBiContrFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  backgroundRiemannBiContrFibFixedFrame (I := I) g₀ (smoothOrthoFrame (I := I) g₁ x) x

omit [CompactSpace M] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem backgroundRiemannBiContrFib_eq_fixedFrame_on_nbhd (g₀ g₁ : SmoothRiemannianMetric I M) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    backgroundRiemannBiContrFib (I := I) g₀ g₁ y =
      backgroundRiemannBiContrFibFixedFrame (I := I) g₀ (smoothOrthoFrame (I := I) g₁ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [backgroundRiemannBiContrFib, backgroundRiemannBiContrFibFixedFrame_toModel, backgroundRiemannBiContrFibFixedFrame_toModel]
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
          ![riemannOp (LeviCivita (I := I) g₀) y (Bf c) (v 0) (v 1), Bf c] =
      ∑ c : Fin (Module.finrank ℝ E),
        backgroundRiemannTraceKernel (I := I) g₀ y D (v 0) (v 1) (Bf c) (Bf c) := by
    intro Bf
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [backgroundRiemannTraceKernel_apply]
  rw [hrewrite (fun c => smoothOrthoFrame (I := I) g₁ y c y),
    hrewrite (fun c => smoothOrthoFrame (I := I) g₁ x₀ c y)]
  rw [orthonormal_basis_bilin_trace (I := I) (M := M) g₁ (x := y)
      (backgroundRiemannTraceKernel (I := I) g₀ y D (v 0) (v 1))
      (fun c => smoothOrthoFrame (I := I) g₁ y c y)
      (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₁ y i j),
    orthonormal_basis_bilin_trace (I := I) (M := M) g₁ (x := y)
      (backgroundRiemannTraceKernel (I := I) g₀ y D (v 0) (v 1))
      (fun c => smoothOrthoFrame (I := I) g₁ x₀ c y)
      (fun i j => smoothOrthoFrame_orthonormal (I := I) g₁ x₀ hy i j)]

omit [CompactSpace M] [I.Boundaryless] in
theorem backgroundRiemannBiContrFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (backgroundRiemannBiContrFib (I := I) g₀ g₁ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (backgroundRiemannBiContrFibFixedFrame (I := I) g₀
          (smoothOrthoFrame (I := I) g₁ x₀) x))) x₀ :=
    backgroundRiemannBiContrFibFixedFrame_contMDiff (I := I) g₀ (smoothOrthoFrame (I := I) g₁ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₁ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (backgroundRiemannBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₀ g₁ x₀ hy))

def ricciArmOrder0BackgroundCurvatureCoeffField (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (backgroundRiemannBiContrFib (I := I) g₀ g₁ x))
      contMDiff_toFun := backgroundRiemannBiContrFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
@[simp] theorem ricciArmOrder0BackgroundCurvatureCoeffField_toSection (g₀ g₁ : SmoothRiemannianMetric I M)
    (x : M) :
    (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (backgroundRiemannBiContrFib (I := I) g₀ g₁ x)) :=
  rfl

end NormedBackgroundRiemannCoefficientField

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_bgRBiContrFib
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x)
    (K J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (backgroundRiemannBiContrFib (I := I) g₀ g₁ x)) n e K J =
      ∑ c : Fin (Module.finrank ℝ E),
        g₀.inner x (e (K 0))
            (riemannOp (LeviCivita (I := I) g₀) x
              (smoothOrthoFrame (I := I) g₁ x c x) (e (J 0)) (e (J 1))) *
          g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x c x) := by
  classical
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (backgroundRiemannBiContrFib (I := I) g₀ g₁ x)) n e K J =
      Tensor0SSpace.toModel
        ((backgroundRiemannBiContrFib (I := I) g₀ g₁ x)
          (coframeS (I := I) (M := M) g₀ x 2 e K))
        (fun i => (e (J i) : E)) := by
    unfold fiberNormSqComponent coframeS; rfl
  rw [hcomp]
  rw [show (backgroundRiemannBiContrFib (I := I) g₀ g₁ x) =
      backgroundRiemannBiContrFibFixedFrame (I := I) g₀ (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [backgroundRiemannBiContrFibFixedFrame_toModel]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hcf : (coframeS (I := I) (M := M) g₀ x 2 e K).toModel
        ![riemannOp (LeviCivita (I := I) g₀) x (smoothOrthoFrame (I := I) g₁ x c x)
              (e (J 0)) (e (J 1)),
          smoothOrthoFrame (I := I) g₁ x c x]
      = g₀.inner x (e (K 0))
          (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g₁ x c x) (e (J 0)) (e (J 1))) *
          g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x c x) := by
    rw [show (coframeS (I := I) (M := M) g₀ x 2 e K).toModel
          ![riemannOp (LeviCivita (I := I) g₀) x (smoothOrthoFrame (I := I) g₁ x c x)
                (e (J 0)) (e (J 1)),
            smoothOrthoFrame (I := I) g₁ x c x]
        = coframeS (I := I) (M := M) g₀ x 2 e K
          ![riemannOp (LeviCivita (I := I) g₀) x (smoothOrthoFrame (I := I) g₁ x c x)
              (e (J 0)) (e (J 1)),
            smoothOrthoFrame (I := I) g₁ x c x] from rfl]
    rw [coframeS_apply, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hcf]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem riemannianFiberNormSq_backgroundRiemannBiContrFib_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (_hδ₀0 : 0 ≤ δ₀) (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (P : SmoothCcTensor g₀ 0 2)
      (_h : ∀ y v w, g₁.inner y v w =
        g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
      {δ : ℝ} (_hδ : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
      (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (backgroundRiemannBiContrFib (I := I) g₀ g₁ x)) ≤ C := by
  classical
  obtain ⟨Kbase, hKbase0, hKbase⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) g₀
  have h1mδ₀ : 0 < 1 - δ₀ := by linarith
  set Bt : ℝ := Real.sqrt Kbase * (1 / (1 - δ₀)) with hBt_def
  refine ⟨((Module.finrank ℝ E : ℝ) ^ 4) * ((Module.finrank ℝ E : ℝ) * Bt) ^ 2,
    by positivity, ?_⟩
  intro g₁ P h δ hδ hδ0 hbound x
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr_v, hsum_rfns⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  have h1mδ : 0 < 1 - δ := by linarith
  have hframe_le : ∀ c : Fin (Module.finrank ℝ E),
      g₀.inner x (smoothOrthoFrame (I := I) g₁ x c x)
          (smoothOrthoFrame (I := I) g₁ x c x) ≤ 1 / (1 - δ₀) := by
    intro c
    set f : TangentSpace I x := smoothOrthoFrame (I := I) g₁ x c x with hf_def
    have hff_nn : 0 ≤ g₀.inner x f f := metric_inner_self_nonneg (I := I) (M := M) g₀ x f
    have hg1 : g₁.inner x f f = 1 := by
      rw [hf_def, smoothOrthoFrame_orthonormal_at_center (I := I) g₁ x c c]; simp
    have htie := h x f f
    have hcc := hbound x f f
    have hcc' : |ccTensorBilinSymm (I := I) g₀ P x f f| ≤ δ * g₀.inner x f f := by
      have heq : δ * Real.sqrt (g₀.inner x f f) * Real.sqrt (g₀.inner x f f)
          = δ * g₀.inner x f f := by rw [mul_assoc, Real.mul_self_sqrt hff_nn]
      rwa [heq] at hcc
    have hlb : -(δ * g₀.inner x f f) ≤ ccTensorBilinSymm (I := I) g₀ P x f f :=
      (abs_le.mp hcc').1
    have h2 : g₁.inner x f f = g₀.inner x f f + ccTensorBilinSymm (I := I) g₀ P x f f := htie
    rw [hg1] at h2
    have hkey : (1 - δ) * g₀.inner x f f ≤ 1 := by nlinarith [hlb, h2]
    have hkey₀ : g₀.inner x f f * (1 - δ₀) ≤ 1 := by
      have hmono : (1 - δ₀) * g₀.inner x f f ≤ (1 - δ) * g₀.inner x f f :=
        mul_le_mul_of_nonneg_right (by linarith) hff_nn
      nlinarith [hmono, hkey]
    rw [le_div_iff₀ h1mδ₀]; exact hkey₀
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 2 2 x
    (show TensorRSSpace 2 2 I x from TensorRSSpace.ofCLM (backgroundRiemannBiContrFib (I := I) g₀ g₁ x))
    e bse hnE hbse horth]
  have heach : ∀ (K J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (backgroundRiemannBiContrFib (I := I) g₀ g₁ x)) n e K J) ^ 2 ≤
        ((Module.finrank ℝ E : ℝ) * Bt) ^ 2 := by
    intro K J
    rw [fiberNormSqComponent_bgRBiContrFib (I := I) g₀ g₁ x e K J]
    have hJ0 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
    have hJ1 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by rw [horth (J 1) (J 1)]; simp
    have hK0 : g₀.inner x (e (K 0)) (e (K 0)) = 1 := by rw [horth (K 0) (K 0)]; simp
    have hK1 : g₀.inner x (e (K 1)) (e (K 1)) = 1 := by rw [horth (K 1) (K 1)]; simp
    have hterm : ∀ c : Fin (Module.finrank ℝ E),
        |g₀.inner x (e (K 0))
            (riemannOp (LeviCivita (I := I) g₀) x
              (smoothOrthoFrame (I := I) g₁ x c x) (e (J 0)) (e (J 1))) *
          g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x c x)| ≤ Bt := by
      intro c
      set f : TangentSpace I x := smoothOrthoFrame (I := I) g₁ x c x with hf_def
      have hff_nn : 0 ≤ g₀.inner x f f := metric_inner_self_nonneg (I := I) (M := M) g₀ x f
      set R0 : TangentSpace I x :=
        riemannOp (LeviCivita (I := I) g₀) x f (e (J 0)) (e (J 1)) with hR0_def
      have hRquad : g₀.inner x R0 R0 ≤ Kbase * g₀.inner x f f := by
        have hk := hKbase x f (e (J 0)) (e (J 1))
        rw [hJ0, hJ1, mul_one, mul_one] at hk
        exact hk
      have hfirst : |g₀.inner x (e (K 0)) R0| ≤ Real.sqrt (Kbase * g₀.inner x f f) := by
        have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (K 0)) R0
        rw [hK0, Real.sqrt_one, one_mul] at hcs
        exact le_trans hcs (Real.sqrt_le_sqrt hRquad)
      have hsecond : |g₀.inner x (e (K 1)) f| ≤ Real.sqrt (g₀.inner x f f) := by
        have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e (K 1)) f
        rw [hK1, Real.sqrt_one, one_mul] at hcs
        exact hcs
      rw [abs_mul]
      calc |g₀.inner x (e (K 0)) R0| * |g₀.inner x (e (K 1)) f|
          ≤ Real.sqrt (Kbase * g₀.inner x f f) * Real.sqrt (g₀.inner x f f) :=
            mul_le_mul hfirst hsecond (abs_nonneg _) (Real.sqrt_nonneg _)
        _ = Real.sqrt Kbase * g₀.inner x f f := by
            rw [Real.sqrt_mul hKbase0, mul_assoc, Real.mul_self_sqrt hff_nn]
        _ ≤ Real.sqrt Kbase * (1 / (1 - δ₀)) :=
            mul_le_mul_of_nonneg_left (hframe_le c) (Real.sqrt_nonneg _)
        _ = Bt := by rw [hBt_def]
    have habs : |∑ c : Fin (Module.finrank ℝ E),
          g₀.inner x (e (K 0))
              (riemannOp (LeviCivita (I := I) g₀) x
                (smoothOrthoFrame (I := I) g₁ x c x) (e (J 0)) (e (J 1))) *
            g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x c x)| ≤
        (Module.finrank ℝ E : ℝ) * Bt := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun c _ => hterm c)) ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  calc ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (backgroundRiemannBiContrFib (I := I) g₀ g₁ x)) n e K J) ^ 2
      ≤ ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n, ((Module.finrank ℝ E : ℝ) * Bt) ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = (Fintype.card (Fin 2 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ) *
          (((Module.finrank ℝ E : ℝ) * Bt) ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
        ring
    _ = ((Module.finrank ℝ E : ℝ) ^ 4) * ((Module.finrank ℝ E : ℝ) * Bt) ^ 2 := by
        have hcard : (Fintype.card (Fin 2 → Fin n) : ℝ) * (Fintype.card (Fin 2 → Fin n) : ℝ)
            = (n : ℝ) ^ 4 := by
          rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
          push_cast; ring
        rw [hcard, ← hnE]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_ricciArmOrder0BackgroundCurvatureCoeffField_realizedFam_riemannianFiberNormSq_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (_hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((ricciArmOrder0BackgroundCurvatureCoeffField (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s)).toSection x) ≤ Λ := by
  classical
  obtain ⟨C, hC0, hbnd⟩ :=
    riemannianFiberNormSq_backgroundRiemannBiContrFib_le (I := I) (M := M) g₀
      (le_max_right δ₀ 0) (max_lt hδ₀ (by norm_num))
  refine ⟨C, hC0, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  set m : ℝ := max δ₀ 0 with hm_def
  have hm0 : 0 ≤ m := le_max_right _ _
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (realizedFam (I := I) g₀ T T' hδ hδ' s).inner y v w =
        g₀.inner y v w +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s) y v w :=
    fun y v w => realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs_mem y v w
  have hδs_raw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  obtain ⟨hs0, hs1⟩ := hs
  have habs_eq : |1 - s| * δ' + |s| * δ = (1 - s) * δ' + s * δ := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
  have hsmall_le : (1 - s) * δ' + s * δ ≤ m := by
    have h1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le (by linarith)
    have h2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have hδ₀_le : δ₀ ≤ m := le_max_left _ _
    nlinarith [h1, h2, hδ₀_le]
  have hδs : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T T' s)) m := by
    intro y v w
    refine le_trans (hδs_raw y v w) ?_
    have hprod : 0 ≤ Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hle' : |1 - s| * δ' + |s| * δ ≤ m := by rw [habs_eq]; exact hsmall_le
    nlinarith [hle', hprod]
  have hmain := hbnd (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) htie (le_of_eq hm_def.symm) hm0 hδs x
  rw [ricciArmOrder0BackgroundCurvatureCoeffField_toSection]
  exact hmain

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
