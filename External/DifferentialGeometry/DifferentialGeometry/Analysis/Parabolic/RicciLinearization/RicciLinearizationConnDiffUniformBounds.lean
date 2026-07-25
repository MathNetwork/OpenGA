import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffCoefficients
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CorrFieldChristoffelCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovGradParametricJointSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovDerivConnDiffQuadraticBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.InverseMetricPerturbationFibreBound
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Geometry.Metric.MetricBounds
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffUniformBoundsSlotPermutations
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffUniformBoundsJointSmoothness
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationConnDiffUniformBoundsFibrePointwiseBound

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
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

section UniformBound

set_option maxRecDepth 16000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private theorem exists_uniformBound_riemannianFiberNormSq_linearizedRicciConnDiffFib_of_jetEnvelope
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δc : ℝ} (_hδc_le : δc ≤ max δ₀ 0)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δc)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle
                (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            (show Tensor0SBundle.TensorRSSpace 2 2 I x from
              linearizedRicciConnDiffOrder0CometricTracedCLM (I := I) g₀ g₁ x) ≤ C ∧
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            (show Tensor0SBundle.TensorRSSpace 3 2 I x from
              linearizedRicciConnDiffOrder1CometricTracedCLM (I := I) g₀ g₁ x) ≤ C := by
  classical
  set δm : ℝ := max δ₀ 0 with hδm_def
  have hδm_nn : 0 ≤ δm := le_max_right _ _
  have hδm_lt : δm < 1 := max_lt hδ₀ one_pos
  have hqpos : (0 : ℝ) < 1 - δm := by linarith
  obtain ⟨C₀, hC₀0, hpw⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδm_nn hδm_lt
  obtain ⟨Ccd, hCcd0, hcd⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB
  set nn : ℝ := (Module.finrank ℝ E : ℝ) with hnn
  have hnn0 : 0 ≤ nn := Nat.cast_nonneg _
  set q : ℝ := 1 / (1 - δm) with hqdef
  have hq0 : 0 ≤ q := le_of_lt (div_pos one_pos hqpos)
  set Mc1 : ℝ := 2 * nn * q * (5 * (nn * (C₀ * B) * 1)) with hMc1
  set Mc0 : ℝ := 2 * nn * q *
    (6 * (nn * (C₀ * B) * (nn * (C₀ * B) * 1)) + 2 * (nn * Ccd * 1)) with hMc0
  have hMc1_nn : 0 ≤ Mc1 := by rw [hMc1]; positivity
  have hMc0_nn : 0 ≤ Mc0 := by rw [hMc0]; positivity
  refine ⟨max (nn ^ 2 * nn ^ 2 * Mc0 ^ 2) (nn ^ 3 * nn ^ 2 * Mc1 ^ 2),
    le_trans (by positivity) (le_max_left _ _), ?_⟩
  intro g₁ P htie δc hδc_le hbound x henv
  letI instT3 : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  have hboundm : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δm := by
    intro y v w'
    refine le_trans (hbound y v w') ?_
    have hnnw : 0 ≤ Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w' w') :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc δc * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w' w')
        = δc * (Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w' w')) := by ring
      _ ≤ δm * (Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w' w')) :=
          mul_le_mul_of_nonneg_right hδc_le hnnw
      _ = δm * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w' w') := by ring
  obtain ⟨n', e, bse, hn, hbse, horth, hpars, hrepr_v, hlastw⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n' = Module.finrank ℝ E := by rw [hn]; rfl
  subst hnE
  set G : ℝ :=
    (letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 3 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
    ‖(show Tensor0SBundle.TensorRSSpace 0 3 I x from
      (iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x)‖) with hG_def
  have hG_nn : 0 ≤ G := by
    rw [hG_def]
    exact norm_nonneg
      (show Tensor0SBundle.TensorRSSpace 0 3 I x from
        (iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x)
  have hG_le : G ≤ B := by
    have hterms : ∀ k ∈ Finset.range 3, 0 ≤
        (letI : Bundle.RiemannianBundle
            (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
        ‖(iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x‖) := by
      intro k _
      letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
      exact norm_nonneg _
    exact le_trans (Finset.single_le_sum hterms
      (show (1 : ℕ) ∈ Finset.range 3 from Finset.mem_range.mpr (by norm_num))) henv
  have hpwA : ∀ v w' : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w')
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w')) ≤
        C₀ * G * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w' w') := by
    intro v w'
    refine le_trans (hpw g₁ P htie (le_refl δm) hδm_nn hboundm x v w') ?_
    rw [hG_def]
  have hpwA' : ∀ (a : Fin (Module.finrank ℝ E)) (v : Fin 2 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel (connDiffFib (I := I) g₁ g₀ x)
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        (C₀ * G) * (Real.sqrt (g₀.inner x (v 0) (v 0)) *
          Real.sqrt (g₀.inner x (v 1) (v 1))) := by
    refine connDiff_flat_factor_bound (I := I) g₀ g₁ x e horth ?_
    intro v w'
    have h := hpwA v w'
    calc Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w')
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x v w'))
        ≤ C₀ * G * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w' w') := h
      _ = (C₀ * G) * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w' w') := by ring
  have hqb : ∀ b : Fin (Module.finrank ℝ E),
      Real.sqrt (g₀.inner x
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)))
          (inverseMetricSharpFib (I := I) g₁ x (g0FlatCLM (I := I) g₀ x (e b)))) ≤ q := by
    intro b
    have h := norm_inverseMetricSharpFib_g0Flat_le (I := I) (M := M) g₀ g₁
      (fun y => ccTensorBilinSymm (I := I) g₀ P y) htie hδm_lt hδm_nn hboundm x (e b)
    have h1b : g₀.inner x (e b) (e b) = 1 := by rw [horth b b]; simp
    rw [h1b, Real.sqrt_one, mul_one] at h
    exact h
  have hDAf : ∀ (a : Fin (Module.finrank ℝ E)) (v : Fin 3 → TangentSpace I x),
      |(Tensor0SBundle.TensorRSSpace.toModel
          ((covGrad (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) g₁ g₀)).toSection x)
          (Tensor0SBundle.Tensor0SSpace.toModel (g0FlatCLM (I := I) g₀ x (e a))))
          (fun j => (v j : E))| ≤
        Ccd * (Real.sqrt (g₀.inner x (v 0) (v 0)) * Real.sqrt (g₀.inner x (v 1) (v 1)) *
          Real.sqrt (g₀.inner x (v 2) (v 2))) := by
    intro a v
    set omg : Tensor0SBundle.Tensor0SSpace 1 I x := g0FlatCLM (I := I) g₀ x (e a) with homg
    have h1 : Tensor0SBundle.TensorRSSpace.toModel
        ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
        (Tensor0SBundle.Tensor0SSpace.toModel omg) =
        Tensor0SBundle.Tensor0SSpace.toModel
          ((show Tensor0SBundle.Tensor0SSpace 1 I x →L[ℝ] Tensor0SBundle.Tensor0SSpace 3 I x from
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x)
            omg) :=
      (toModel_tensorRS_apply (I := I) 1 3 x _ omg).symm
    rw [h1]
    obtain ⟨om, hom⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := Tensor0SBundle.Tensor0SModel 1 ℝ E)
      (V := fun y : M => Tensor0SBundle.Tensor0SSpace 1 I y) x omg
    set X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x (v 0),
        smoothExtensionTangent_contMDiff (I := I) x (v 0)⟩ with hX
    set Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x (v 1),
        smoothExtensionTangent_contMDiff (I := I) x (v 1)⟩ with hY
    set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
      ⟨smoothExtensionTangent (I := I) x (v 2),
        smoothExtensionTangent_contMDiff (I := I) x (v 2)⟩ with hZ
    have hXx : X x = v 0 := smoothExtensionTangent_eq (I := I) x (v 0)
    have hYx : Y x = v 1 := smoothExtensionTangent_eq (I := I) x (v 1)
    have hZx : Z x = v 2 := smoothExtensionTangent_eq (I := I) x (v 2)
    have hbr := connDiffSection_covGrad_eq_covDerivConnDiff (I := I) g₁ g₀ om X Y Z x
    rw [hom, hXx, hYx, hZx] at hbr
    have hargs : (fun j : Fin 3 => (v j : E)) =
        (Fin.cons (v 0) (Fin.cons (v 1) ![v 2]) : Fin 3 → TangentSpace I x) := by
      funext j
      fin_cases j <;> rfl
    rw [hargs, hbr]
    set vec : TangentSpace I x := covDerivConnDiff (I := I) g₀ g₁ X Z Y x with hvec
    rw [show omg (fun _ : Fin 1 => vec) =
        cotangentToDual (I := I) (x := x) omg vec from
      (cotangentToDual_apply (I := I) (x := x) omg vec).symm]
    rw [homg, cotangentToDual_g0FlatCLM]
    have hcs := abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x (e a) vec
    have h1a : g₀.inner x (e a) (e a) = 1 := by rw [horth a a]; simp
    rw [h1a, Real.sqrt_one, one_mul] at hcs
    refine le_trans hcs ?_
    have hengine := hcd g₁ P hδc_le hbound htie x henv (v 0) (v 2) (v 1)
    have hveceq : covDerivConnDiff (I := I) g₀ g₁
        (smoothExtensionTangent (I := I) x (v 0))
        (smoothExtensionTangent (I := I) x (v 2))
        (smoothExtensionTangent (I := I) x (v 1)) x = vec := rfl
    rw [hveceq] at hengine
    refine le_trans hengine (le_of_eq ?_)
    ring
  set A : Tensor0SBundle.TensorRSSpace 1 2 I x :=
    (connDiffSection (I := I) g₁ g₀).toSection x with hAset
  set DAv : Tensor0SBundle.TensorRSSpace 1 3 I x :=
    (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x with hDAset
  have hCA_nn : 0 ≤ C₀ * G := mul_nonneg hC₀0 hG_nn
  have hCAB : C₀ * G ≤ C₀ * B := mul_le_mul_of_nonneg_left hG_le hC₀0
  have hO1 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from
        linearizedRicciConnDiffOrder1CometricTracedCLM (I := I) g₀ g₁ x) ≤ nn ^ 3 * nn ^ 2 * Mc1 ^ 2 := by
    rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 3 2 x
      (show Tensor0SBundle.TensorRSSpace 3 2 I x from
        linearizedRicciConnDiffOrder1CometricTracedCLM (I := I) g₀ g₁ x) e bse rfl hbse horth]
    have hcompb : ∀ (K : Fin 3 → Fin (Module.finrank ℝ E))
        (J : Fin 2 → Fin (Module.finrank ℝ E)),
        (fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
          (show Tensor0SBundle.TensorRSSpace 3 2 I x from
            linearizedRicciConnDiffOrder1CometricTracedCLM (I := I) g₀ g₁ x)
          (Module.finrank ℝ E) e K J) ^ 2 ≤ Mc1 ^ 2 := by
      intro K J
      have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
          (show Tensor0SBundle.TensorRSSpace 3 2 I x from
            linearizedRicciConnDiffOrder1CometricTracedCLM (I := I) g₀ g₁ x)
          (Module.finrank ℝ E) e K J =
          Tensor0SBundle.Tensor0SSpace.toModel
            (ricciCometricFourTraceCLM (I := I) g₁ x
              (linearizedRicciConnDiffOrder1CLM (I := I) x A
                (coframeS (I := I) (M := M) g₀ x 3 e K)))
            (fun j => ((e (J j) : TangentSpace I x) : E)) := rfl
      have hfpb := fibPointwiseBound_order1CLM (I := I) g₀ x e horth hrepr_v A hCA_nn hpwA'
        (fibPointwiseBound_coframe (I := I) g₀ x 3 e horth K)
      have hb := fourTrace_toModel_bound (I := I) g₀ g₁ x e horth hrepr_v hq0 hqb hfpb
        (fun j => e (J j))
      have hJ0 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
      have hJ1 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by rw [horth (J 1) (J 1)]; simp
      rw [hJ0, hJ1, Real.sqrt_one, mul_one, mul_one] at hb
      have hb2 : |Tensor0SBundle.Tensor0SSpace.toModel
          (ricciCometricFourTraceCLM (I := I) g₁ x
            (linearizedRicciConnDiffOrder1CLM (I := I) x A
              (coframeS (I := I) (M := M) g₀ x 3 e K)))
          (fun j => ((e (J j) : TangentSpace I x) : E))| ≤ Mc1 := by
        refine le_trans hb ?_
        rw [hMc1, hnn]
        have hkey : (0 : ℝ) ≤ 10 * (Module.finrank ℝ E : ℝ) ^ 2 * q * (C₀ * B - C₀ * G) :=
          mul_nonneg (mul_nonneg (by positivity) hq0) (sub_nonneg.mpr hCAB)
        linarith [hkey]
      rw [hcomp]
      have h2 := abs_le.mp hb2
      exact sq_le_sq' h2.1 h2.2
    calc (∑ K : Fin 3 → Fin (Module.finrank ℝ E), ∑ J : Fin 2 → Fin (Module.finrank ℝ E),
          (fiberNormSqComponent (I := I) (M := M) g₀ x 3 2
            (show Tensor0SBundle.TensorRSSpace 3 2 I x from
              linearizedRicciConnDiffOrder1CometricTracedCLM (I := I) g₀ g₁ x)
            (Module.finrank ℝ E) e K J) ^ 2)
        ≤ ∑ _K : Fin 3 → Fin (Module.finrank ℝ E), ∑ _J : Fin 2 → Fin (Module.finrank ℝ E),
            Mc1 ^ 2 :=
          Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => hcompb K J))
      _ = nn ^ 3 * nn ^ 2 * Mc1 ^ 2 := by
          rw [Finset.sum_const, Finset.sum_const]
          simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_pow]
          rw [hnn]
          ring
  have hO0 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from
        linearizedRicciConnDiffOrder0CometricTracedCLM (I := I) g₀ g₁ x) ≤ nn ^ 2 * nn ^ 2 * Mc0 ^ 2 := by
    rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 2 2 x
      (show Tensor0SBundle.TensorRSSpace 2 2 I x from
        linearizedRicciConnDiffOrder0CometricTracedCLM (I := I) g₀ g₁ x) e bse rfl hbse horth]
    have hcompb : ∀ (K : Fin 2 → Fin (Module.finrank ℝ E))
        (J : Fin 2 → Fin (Module.finrank ℝ E)),
        (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
          (show Tensor0SBundle.TensorRSSpace 2 2 I x from
            linearizedRicciConnDiffOrder0CometricTracedCLM (I := I) g₀ g₁ x)
          (Module.finrank ℝ E) e K J) ^ 2 ≤ Mc0 ^ 2 := by
      intro K J
      have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
          (show Tensor0SBundle.TensorRSSpace 2 2 I x from
            linearizedRicciConnDiffOrder0CometricTracedCLM (I := I) g₀ g₁ x)
          (Module.finrank ℝ E) e K J =
          Tensor0SBundle.Tensor0SSpace.toModel
            (ricciCometricFourTraceCLM (I := I) g₁ x
              (linearizedRicciConnDiffOrder0CLM (I := I) x A DAv
                (coframeS (I := I) (M := M) g₀ x 2 e K)))
            (fun j => ((e (J j) : TangentSpace I x) : E)) := rfl
      have hfpb := fibPointwiseBound_order0CLM (I := I) g₀ x e horth hrepr_v A hCA_nn hpwA'
        DAv hCcd0 hDAf (fibPointwiseBound_coframe (I := I) g₀ x 2 e horth K)
      have hb := fourTrace_toModel_bound (I := I) g₀ g₁ x e horth hrepr_v hq0 hqb hfpb
        (fun j => e (J j))
      have hJ0 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by rw [horth (J 0) (J 0)]; simp
      have hJ1 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by rw [horth (J 1) (J 1)]; simp
      rw [hJ0, hJ1, Real.sqrt_one, mul_one, mul_one] at hb
      have hb2 : |Tensor0SBundle.Tensor0SSpace.toModel
          (ricciCometricFourTraceCLM (I := I) g₁ x
            (linearizedRicciConnDiffOrder0CLM (I := I) x A DAv
              (coframeS (I := I) (M := M) g₀ x 2 e K)))
          (fun j => ((e (J j) : TangentSpace I x) : E))| ≤ Mc0 := by
        refine le_trans hb ?_
        rw [hMc0, hnn]
        have hsq : C₀ * G * (C₀ * G) ≤ C₀ * B * (C₀ * B) :=
          mul_le_mul hCAB hCAB hCA_nn (le_trans hCA_nn hCAB)
        have hkey : (0 : ℝ) ≤ 12 * (Module.finrank ℝ E : ℝ) ^ 3 * q *
            (C₀ * B * (C₀ * B) - C₀ * G * (C₀ * G)) :=
          mul_nonneg (mul_nonneg (by positivity) hq0) (sub_nonneg.mpr hsq)
        linarith [hkey]
      rw [hcomp]
      have h2 := abs_le.mp hb2
      exact sq_le_sq' h2.1 h2.2
    calc (∑ K : Fin 2 → Fin (Module.finrank ℝ E), ∑ J : Fin 2 → Fin (Module.finrank ℝ E),
          (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
            (show Tensor0SBundle.TensorRSSpace 2 2 I x from
              linearizedRicciConnDiffOrder0CometricTracedCLM (I := I) g₀ g₁ x)
            (Module.finrank ℝ E) e K J) ^ 2)
        ≤ ∑ _K : Fin 2 → Fin (Module.finrank ℝ E), ∑ _J : Fin 2 → Fin (Module.finrank ℝ E),
            Mc0 ^ 2 :=
          Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => hcompb K J))
      _ = nn ^ 2 * nn ^ 2 * Mc0 ^ 2 := by
          rw [Finset.sum_const, Finset.sum_const]
          simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
            Nat.cast_pow]
          rw [hnn]
          ring
  exact ⟨le_trans hO0 (le_max_left _ _), le_trans hO1 (le_max_right _ _)⟩

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem exists_uniformBound_sqrt_riemannianFiberNormSq_linearizedRicciConnDiffCoeff_realizedFam_of_jetEnvelope
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
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤
            Λ ∧
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
              ((linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s).toSection x)) ≤
            Λ := by
  classical
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) (M := M) g₀ a ha_super
  obtain ⟨C, hC0, hcore⟩ :=
    exists_uniformBound_riemannianFiberNormSq_linearizedRicciConnDiffFib_of_jetEnvelope (I := I) (M := M) g₀ hδ₀ (Csob * R)
      (by positivity)
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
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
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
  have hsmall_le : |1 - s| * δ' + |s| * δ ≤ max δ₀ 0 := by
    rw [habs_eq]
    have h1 : (1 - s) * δ' ≤ (1 - s) * δ₀ := mul_le_mul_of_nonneg_left hδ'_le (by linarith)
    have h2 : s * δ ≤ s * δ₀ := mul_le_mul_of_nonneg_left hδ_le hs0
    have hδ₀_le : δ₀ ≤ max δ₀ 0 := le_max_left _ _
    nlinarith [h1, h2, hδ₀_le]
  have henv := hCsob T T' hR hTball hT'ball s ⟨hs0, hs1⟩ x
  have hmain := hcore (realizedFam (I := I) g₀ T T' hδ hδ' s)
    (convexPerturbation (I := I) g₀ T T' s) htie hsmall_le hδs_raw x henv
  constructor
  · have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((linearizedRicciConnDiffOrder0Coeff (I := I) g₀ T T' hδ hδ' s).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (show Tensor0SBundle.TensorRSSpace 2 2 I x from
            linearizedRicciConnDiffOrder0CometricTracedCLM (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) x) := rfl
    rw [h0]
    exact Real.sqrt_le_sqrt hmain.1
  · have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
        ((linearizedRicciConnDiffOrder1Coeff (I := I) g₀ T T' hδ hδ' s).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
          (show Tensor0SBundle.TensorRSSpace 3 2 I x from
            linearizedRicciConnDiffOrder1CometricTracedCLM (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) x) := rfl
    rw [h1]
    exact Real.sqrt_le_sqrt hmain.2
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem ricci_coeff_rfns_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δc : ℝ} (_hδc_le : δc ≤ max δ₀ 0)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δc)
        (x : M),
        (∑ j ∈ Finset.range 3,
            (letI : Bundle.RiemannianBundle
                (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + j) I b) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + j)
            ‖(iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x‖)) ≤ B →
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
            (show Tensor0SBundle.TensorRSSpace 2 2 I x from
              linearizedRicciConnDiffOrder0CometricTracedCLM (I := I) g₀ g₁ x) ≤ C ∧
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x
            (show Tensor0SBundle.TensorRSSpace 3 2 I x from
              linearizedRicciConnDiffOrder1CometricTracedCLM (I := I) g₀ g₁ x) ≤ C := by
  exact
    exists_uniformBound_riemannianFiberNormSq_linearizedRicciConnDiffFib_of_jetEnvelope
      (I := I) (M := M) g₀ hδ₀ B hB


end UniformBound

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
