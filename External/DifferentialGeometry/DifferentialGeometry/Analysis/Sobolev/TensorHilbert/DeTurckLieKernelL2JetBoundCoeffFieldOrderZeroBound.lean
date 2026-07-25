import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovDerivConnDiffQuadraticBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ConvexPerturbationPointwiseC2
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqRiemannOpDualFrameParseval
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SingleSlotOperatorFiberNormBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckLinearization
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.BracketDivergenceForm


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (connDiffCovDerivBiContrFib dLaBiContrFib_contMDiff deTurckLieDLbFib deTurckLieDLbFib_contMDiff
    deTurckLieFib deTurckLieCoeffField deTurckLieCoeffField_toSection
    deTurckConnDiffCovDeriv connDiff_pairing_mdiffAt connDiffCovDerivOp dLaCovKernel_apply_extend)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def deTurckLieConnDiffDerivCoeffField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (connDiffCovDerivBiContrFib (I := I) g₁ g_bg x))
      contMDiff_toFun := dLaBiContrFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
@[simp] theorem deTurckLieDLaCoeffField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (connDiffCovDerivBiContrFib (I := I) g₁ g_bg x)) := rfl

def deTurckLieDLbCoeffField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x))
      contMDiff_toFun := deTurckLieDLbFib_contMDiff (I := I) g₁ g_bg }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem deTurckLieDLbCoeffField_toSection
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (deTurckLieDLbFib (I := I) g₁ g_bg x)) := rfl

omit [I.Boundaryless] in
theorem deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg +
        deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg =
      deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    deTurckLieDLaCoeffField_toSection, deTurckLieDLbCoeffField_toSection,
    deTurckLieCoeffField_toSection]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem connDiff_cocycle (gA gB gC : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    PDE.DeTurck.connDiff (I := I) gA gB x u v + PDE.DeTurck.connDiff (I := I) gB gC x u v =
      PDE.DeTurck.connDiff (I := I) gA gC x u v := by
  classical
  have hσ := smoothExtensionTangent_mdiff (I := I) x u x
  have hu : smoothExtensionTangent (I := I) x u x = u :=
    smoothExtensionTangent_eq (I := I) x u
  rw [← hu]
  rw [PDE.DeTurck.connDiff_apply (I := I) gA gB hσ v,
    PDE.DeTurck.connDiff_apply (I := I) gB gC hσ v,
    PDE.DeTurck.connDiff_apply (I := I) gA gC hσ v]
  abel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckLieCovDerivA_backgroundSplit
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (X P Q : Π b : M, TangentSpace I b) (x : M)
    (hP : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (P b)) x)
    (hQ : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun b => TotalSpace.mk' E (E := TangentSpace I) b (Q b)) x) :
    deTurckConnDiffCovDeriv (I := I) g₁ g_bg X P Q x =
      covDerivConnDiff (I := I) g₀ g₁ X Q P x
        - covDerivConnDiff (I := I) g₀ g_bg X Q P x
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x) (Q x)) (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x) (X x)) (Q x)
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Q x) (X x)) := by
  classical
  have hσ := connDiff_pairing_mdiffAt (I := I) g₁ g_bg hP hQ
  have hσB := connDiff_pairing_mdiffAt (I := I) g_bg g₀ hP hQ
  have hsum : (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (P b) (Q b)) =
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b))
        + (fun b : M => PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)) := by
    funext b
    change PDE.DeTurck.connDiff (I := I) g₁ g₀ b (P b) (Q b) =
      PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)
        + PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)
    exact (connDiff_cocycle (I := I) g₁ g_bg g₀ b (P b) (Q b)).symm
  have hadd := (LeviCivita (I := I) g₀).isCovariantDerivativeOnUniv.add
    (σ := fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b))
    (σ' := fun b : M => PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)) hσ hσB
  have hsplit : (LeviCivita (I := I) g₀).toFun
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (P b) (Q b)) x (X x)
        - (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)) x (X x) := by
    have h3 : (LeviCivita (I := I) g₀).toFun
        (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (P b) (Q b)) x (X x)
        = (LeviCivita (I := I) g₀).toFun
            (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
          + (LeviCivita (I := I) g₀).toFun
            (fun b : M => PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)) x (X x) := by
      rw [hsum]
      have h2 := congrArg (fun L => L (X x)) hadd
      simpa using h2
    rw [h3]
    abel
  have hout' : (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x) (Q x)) (X x) := by
    have h : PDE.DeTurck.connDiff (I := I) g₁ g₀ x
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x) (Q x)) (X x)
        = (LeviCivita (I := I) g₁).toFun
            (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
          - (LeviCivita (I := I) g₀).toFun
            (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x) :=
      PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := fun b : M =>
        PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) hσ (X x)
    rw [h]
    abel
  have hinnP' : (LeviCivita (I := I) g₁).toFun P x (X x)
      = (LeviCivita (I := I) g₀).toFun P x (X x)
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x) (X x) := by
    have h : PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x) (X x)
        = (LeviCivita (I := I) g₁).toFun P x (X x)
          - (LeviCivita (I := I) g₀).toFun P x (X x) :=
      PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := P) hP (X x)
    rw [h]
    abel
  have hinnQ' : (LeviCivita (I := I) g₁).toFun Q x (X x)
      = (LeviCivita (I := I) g₀).toFun Q x (X x)
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Q x) (X x) := by
    have h : PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Q x) (X x)
        = (LeviCivita (I := I) g₁).toFun Q x (X x)
          - (LeviCivita (I := I) g₀).toFun Q x (X x) :=
      PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ (σ := Q) hQ (X x)
    rw [h]
    abel
  have hsplitT2 : PDE.DeTurck.connDiff (I := I) g₁ g_bg x
      ((LeviCivita (I := I) g₀).toFun P x (X x)
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x) (X x)) (Q x)
      = PDE.DeTurck.connDiff (I := I) g₁ g_bg x
          ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
        + PDE.DeTurck.connDiff (I := I) g₁ g_bg x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x) (X x)) (Q x) := by
    rw [map_add]
    rfl
  have hsplitT3 : PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
      ((LeviCivita (I := I) g₀).toFun Q x (X x)
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Q x) (X x))
      = PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
          ((LeviCivita (I := I) g₀).toFun Q x (X x))
        + PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Q x) (X x)) :=
    map_add _ _ _
  have hT2c : PDE.DeTurck.connDiff (I := I) g₁ g_bg x
      ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
      = PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
        - PDE.DeTurck.connDiff (I := I) g_bg g₀ x
            ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x) := by
    have h := connDiff_cocycle (I := I) g₁ g_bg g₀ x
      ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x)
    rw [← h]
    abel
  have hT3c : PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
      ((LeviCivita (I := I) g₀).toFun Q x (X x))
      = PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x)
          ((LeviCivita (I := I) g₀).toFun Q x (X x))
        - PDE.DeTurck.connDiff (I := I) g_bg g₀ x (P x)
            ((LeviCivita (I := I) g₀).toFun Q x (X x)) := by
    have h := connDiff_cocycle (I := I) g₁ g_bg g₀ x (P x)
      ((LeviCivita (I := I) g₀).toFun Q x (X x))
    rw [← h]
    abel
  have hA : covDerivConnDiff (I := I) g₀ g₁ X Q P x
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ b (P b) (Q b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (P x)
            ((LeviCivita (I := I) g₀).toFun Q x (X x))
        - PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x) := rfl
  have hB : covDerivConnDiff (I := I) g₀ g_bg X Q P x
      = (LeviCivita (I := I) g₀).toFun
          (fun b : M => PDE.DeTurck.connDiff (I := I) g_bg g₀ b (P b) (Q b)) x (X x)
        - PDE.DeTurck.connDiff (I := I) g_bg g₀ x (P x)
            ((LeviCivita (I := I) g₀).toFun Q x (X x))
        - PDE.DeTurck.connDiff (I := I) g_bg g₀ x
            ((LeviCivita (I := I) g₀).toFun P x (X x)) (Q x) := rfl
  change (LeviCivita (I := I) g₁).toFun
      (fun b : M => PDE.DeTurck.connDiff (I := I) g₁ g_bg b (P b) (Q b)) x (X x)
      - PDE.DeTurck.connDiff (I := I) g₁ g_bg x
          ((LeviCivita (I := I) g₁).toFun P x (X x)) (Q x)
      - PDE.DeTurck.connDiff (I := I) g₁ g_bg x (P x)
          ((LeviCivita (I := I) g₁).toFun Q x (X x)) = _
  rw [hout', hinnP', hinnQ', hsplitT2, hsplitT3, hT2c, hT3c, hsplit, hA, hB]
  abel

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem dLaCovKernel_backgroundSplit (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 p q : TangentSpace I x) :
    connDiffCovDerivOp (I := I) g₁ g_bg x v0 p q =
      covDerivConnDiff (I := I) g₀ g₁
          (smoothExtensionTangent (I := I) x v0)
          (smoothExtensionTangent (I := I) x q)
          (smoothExtensionTangent (I := I) x p) x
        - covDerivConnDiff (I := I) g₀ g_bg
            (smoothExtensionTangent (I := I) x v0)
            (smoothExtensionTangent (I := I) x q)
            (smoothExtensionTangent (I := I) x p) x
        + PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g_bg x p q) v0
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x p v0) q
        - PDE.DeTurck.connDiff (I := I) g₁ g_bg x p
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x q v0) := by
  rw [dLaCovKernel_apply_extend (I := I) g₁ g_bg x v0 p q]
  rw [deTurckLieCovDerivA_backgroundSplit (I := I) g₀ g₁ g_bg
    (smoothExtensionTangent (I := I) x v0)
    (smoothExtensionTangent (I := I) x p)
    (smoothExtensionTangent (I := I) x q) x
    (smoothExtensionTangent_mdiff (I := I) x p x)
    (smoothExtensionTangent_mdiff (I := I) x q x)]
  simp only [smoothExtensionTangent_eq]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (realizedFam convexPerturbation realizedFam_inner_of_mem convexPerturbation_gFibreOpBound_abs
    abs_convex_smallConstant_lt_one realizedSmallSet)
open DifferentialGeometry.Analysis.Laplacian (metric_inner_self_nonneg metric_inner_cauchy_schwarz_sq)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one dLaBiContrFibFixedFrame_toModel)
open DifferentialGeometry.Geometry.Curvature
  (exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
  (g0FlatCLM cotangentToDual_g0FlatCLM g0FlatCLM_apply)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem abs_metric_inner_le (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    |g.inner x u v| ≤ Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x v v) := by
  have h2 := metric_inner_cauchy_schwarz_sq (I := I) (M := M) g x u v
  have habs : |g.inner x u v| = Real.sqrt ((g.inner x u v) ^ 2) :=
    (Real.sqrt_sq_eq_abs _).symm
  rw [habs]
  refine le_trans (Real.sqrt_le_sqrt h2) ?_
  rw [Real.sqrt_mul (metric_inner_self_nonneg (I := I) (M := M) g x u)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem sqrt_metric_inner_add_le (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    Real.sqrt (g.inner x (u + v) (u + v)) ≤
      Real.sqrt (g.inner x u u) + Real.sqrt (g.inner x v v) := by
  have huu := metric_inner_self_nonneg (I := I) (M := M) g x u
  have hvv := metric_inner_self_nonneg (I := I) (M := M) g x v
  have hexp : g.inner x (u + v) (u + v) =
      g.inner x u u + g.inner x u v + (g.inner x v u + g.inner x v v) := by
    simp only [map_add, ContinuousLinearMap.add_apply]
    ring
  have hsymm : g.inner x v u = g.inner x u v := g.symm x v u
  have hcs := abs_metric_inner_le (I := I) (M := M) g x u v
  have hsq : g.inner x (u + v) (u + v) ≤
      (Real.sqrt (g.inner x u u) + Real.sqrt (g.inner x v v)) ^ 2 := by
    rw [hexp, hsymm]
    have h1 := Real.sq_sqrt huu
    have h2 := Real.sq_sqrt hvv
    have h3 := abs_le.mp hcs
    nlinarith [h3.2, Real.sqrt_nonneg (g.inner x u u), Real.sqrt_nonneg (g.inner x v v)]
  refine le_trans (Real.sqrt_le_sqrt hsq) ?_
  rw [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem sqrt_metric_inner_sub_le (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    Real.sqrt (g.inner x (u - v) (u - v)) ≤
      Real.sqrt (g.inner x u u) + Real.sqrt (g.inner x v v) := by
  have hneg : g.inner x (-v) (-v) = g.inner x v v := by
    simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg]
  have h := sqrt_metric_inner_add_le (I := I) (M := M) g x u (-v)
  rw [← sub_eq_add_neg] at h
  rw [hneg] at h
  exact h

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem gFibreOpBound_mono_of_le (g₀ : SmoothRiemannianMetric I M)
    (h : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    {δ δ' : ℝ} (hle : δ ≤ δ')
    (hb : metricCauchySchwarzBound (I := I) (M := M) g₀ h δ) :
    metricCauchySchwarzBound (I := I) (M := M) g₀ h δ' := by
  intro y a b
  refine le_trans (hb y a b) ?_
  have hnn : 0 ≤ Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc δ * Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)
      = δ * (Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)) := by ring
    _ ≤ δ' * (Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b)) :=
        mul_le_mul_of_nonneg_right hle hnn
    _ = δ' * Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) := by ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem abs_g1_inner_le_two_sqrt (g₀ g₁ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
    {δs : ℝ} (hδs1 : δs ≤ 1)
    (hb : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δs)
    (x : M) (u w : TangentSpace I x) :
    |g₁.inner x u w| ≤
      2 * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x w w)) := by
  rw [htie x u w]
  refine le_trans (abs_add_le _ _) ?_
  have h1 := abs_metric_inner_le (I := I) (M := M) g₀ x u w
  have h2 := hb x u w
  have hnn : 0 ≤ Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [h1, h2, hnn]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem coframeS_one_eq_g0FlatCLM_local
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 1 → Fin n) :
    coframeS (I := I) (M := M) g₀ x 1 e K = g0FlatCLM (I := I) g₀ x (e (K 0)) := by
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply, cotangentToDual_apply,
    cotangentToDual_apply]
  rw [show coframeS (I := I) (M := M) g₀ x 1 e K (fun _ : Fin 1 => w) =
      ∏ k : Fin 1, g₀.inner x (e (K k)) w from coframeS_apply (I := I) (M := M) g₀ x 1 e K _]
  rw [Fin.prod_univ_one]
  rw [g0FlatCLM_apply, dualToCotangent_apply]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem toModel_coframeS_two (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 2 → Fin n)
    (p q : TangentSpace I x) :
    Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K) ![(p : E), (q : E)] =
      g₀.inner x (e (K 0)) p * g₀.inner x (e (K 1)) q := by
  rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K) ![(p : E), (q : E)] =
      coframeS (I := I) (M := M) g₀ x 2 e K ![p, q] from rfl]
  rw [coframeS_apply (I := I) (M := M) g₀ x 2 e K ![p, q], Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem abs_tensor12_flat_eval_le_fibreNorm_mul_sqrt_local
    (g₀ : SmoothRiemannianMetric I M) (x : M)
    (W : TensorRSSpace 1 2 I x) (d a b : TangentSpace I x) :
    letI : Bundle.RiemannianBundle
        (fun y : M => Tensor0SBundle.TensorRSSpace 1 2 I y) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 1 2
    |Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
          (g0FlatCLM (I := I) g₀ x d))
        (Fin.cons a ![b])| ≤
      ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ *
        Real.sqrt (g₀.inner x d d) *
        Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 1 2 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 1 2
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  set vec : Fin 2 → TangentSpace I x := ![a, b] with hvec_def
  set coef : (Fin 1 → Fin n) × (Fin 2 → Fin n) → ℝ :=
    fun p => g₀.inner x (e (p.1 0)) d * ∏ i : Fin 2, g₀.inner x (e (p.2 i)) (vec i) with hcoef_def
  set comp : (Fin 1 → Fin n) × (Fin 2 → Fin n) → ℝ :=
    fun p => fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e p.1 p.2 with hcomp_def
  have hcompval : ∀ (K : Fin 1 → Fin n) (J : Fin 2 → Fin n),
      fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e K J =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
            (g0FlatCLM (I := I) g₀ x (e (K 0))))
          (fun i : Fin 2 => e (J i)) := by
    intro K J
    rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e K J =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
            (coframeS (I := I) (M := M) g₀ x 1 e K))
          (fun i : Fin 2 => e (J i)) from rfl]
    rw [coframeS_one_eq_g0FlatCLM_local (I := I) (M := M) g₀ x e K]
  have hWd : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
        (g0FlatCLM (I := I) g₀ x d) =
      ∑ k : Fin n, g₀.inner x (e k) d •
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
          (g0FlatCLM (I := I) g₀ x (e k)) := by
    have hflat : g0FlatCLM (I := I) g₀ x d =
        ∑ k : Fin n, g₀.inner x (e k) d • g0FlatCLM (I := I) g₀ x (e k) := by
      conv_lhs => rw [hrepr d]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul]
    rw [hflat, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul]
  have hexp : ∀ i : Fin 2, vec i = ∑ j : Fin n, g₀.inner x (e j) (vec i) • e j :=
    fun i => hrepr (vec i)
  have hvalue : Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
          (g0FlatCLM (I := I) g₀ x d))
        (Fin.cons a ![b]) =
      ∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p := by
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
          (g0FlatCLM (I := I) g₀ x d)) vec =
        ∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p
    rw [hWd]
    rw [show Tensor0SSpace.toModel
          (∑ k : Fin n, g₀.inner x (e k) d •
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
              (g0FlatCLM (I := I) g₀ x (e k))) =
        ∑ k : Fin n, g₀.inner x (e k) d •
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
              (g0FlatCLM (I := I) g₀ x (e k))) from by
      rw [← Tensor0SSpace.toModelL_apply, map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_smul, Tensor0SSpace.toModelL_apply]]
    rw [ContinuousMultilinearMap.sum_apply]
    have hterm : ∀ k : Fin n,
        (g₀.inner x (e k) d •
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
              (g0FlatCLM (I := I) g₀ x (e k)))) vec =
        ∑ J : Fin 2 → Fin n,
          (g₀.inner x (e k) d * ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i)) *
            fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e (fun _ => k) J := by
      intro k
      rw [ContinuousMultilinearMap.smul_apply]
      set B2 : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
            (g0FlatCLM (I := I) g₀ x (e k))) with hB2_def
      set coefJ : (Fin 2 → Fin n) → ℝ :=
        fun J => ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) with hcoefJ_def
      set compJ : (Fin 2 → Fin n) → ℝ :=
        fun J => B2 (fun i : Fin 2 => (show E from e (J i))) with hcompJ_def
      have hexp' : ∀ i : Fin 2, (show E from vec i) =
          ∑ j : Fin n, g₀.inner x (e j) (vec i) • (show E from e j) :=
        fun i => hexp i
      have hB2val : B2 vec = ∑ J : Fin 2 → Fin n, coefJ J * compJ J := by
        have hrw : B2 vec = B2 (fun i : Fin 2 =>
            ∑ j : Fin n, g₀.inner x (e j) (vec i) • (show E from e j)) := by
          congr 1
          funext i
          exact hexp' i
        rw [hrw, ContinuousMultilinearMap.map_sum]
        refine Finset.sum_congr rfl (fun J _ => ?_)
        rw [hcoefJ_def, hcompJ_def]
        rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
      rw [hB2val, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun J _ => ?_)
      rw [hcompJ_def, hcompval (fun _ => k) J, ← hB2_def, hcoefJ_def]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    rw [show (∑ k : Fin n, ∑ J : Fin 2 → Fin n,
          (g₀.inner x (e k) d * ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i)) *
            fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e (fun _ => k) J) =
        ∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n,
          (g₀.inner x (e (K 0)) d * ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i)) *
            fiberNormSqComponent (I := I) (M := M) g₀ x 1 2 W n e K J from by
      refine (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n)).symm _ _ (fun k => ?_))
      refine Finset.sum_congr rfl (fun J _ => ?_)
      have hKeq : (Equiv.funUnique (Fin 1) (Fin n)).symm k = (fun _ : Fin 1 => k) := rfl
      rw [hKeq]]
    rw [← Fintype.sum_prod_type']
  rw [hvalue]
  have hCS : (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p) ^ 2 ≤
      (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p ^ 2) *
        ∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), comp p ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ coef comp
  have hdd_nn : 0 ≤ g₀.inner x d d := metric_inner_self_nonneg (I := I) (M := M) g₀ x d
  have haa_nn : 0 ≤ g₀.inner x a a := metric_inner_self_nonneg (I := I) (M := M) g₀ x a
  have hbb_nn : 0 ≤ g₀.inner x b b := metric_inner_self_nonneg (I := I) (M := M) g₀ x b
  have hcoefsq : (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p ^ 2) =
      g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b) := by
    have hpow : ∀ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p ^ 2 =
        g₀.inner x (e (p.1 0)) d ^ 2 *
          ∏ i : Fin 2, g₀.inner x (e (p.2 i)) (vec i) ^ 2 := by
      intro p
      rw [hcoef_def, mul_pow, ← Finset.prod_pow]
    rw [Finset.sum_congr rfl (fun p _ => hpow p)]
    rw [Fintype.sum_prod_type]
    rw [show (∑ K : Fin 1 → Fin n, ∑ J : Fin 2 → Fin n,
          g₀.inner x (e (K 0)) d ^ 2 * ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) ^ 2) =
        (∑ K : Fin 1 → Fin n, g₀.inner x (e (K 0)) d ^ 2) *
          ∑ J : Fin 2 → Fin n, ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) ^ 2 from by
      rw [Finset.sum_mul_sum]]
    have hKsum : (∑ K : Fin 1 → Fin n, g₀.inner x (e (K 0)) d ^ 2) = g₀.inner x d d := by
      rw [← hpars d]
      rw [show (∑ K : Fin 1 → Fin n, g₀.inner x (e (K 0)) d ^ 2) =
          ∑ k : Fin n, g₀.inner x (e k) d ^ 2 from by
        rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin n))
          (fun k : Fin n => g₀.inner x (e k) d ^ 2)]
        rfl]
    have hJsum : (∑ J : Fin 2 → Fin n, ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) ^ 2) =
        g₀.inner x a a * g₀.inner x b b := by
      rw [show (∑ J : Fin 2 → Fin n, ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) ^ 2) =
          ∑ J ∈ Fintype.piFinset (fun _ : Fin 2 => (Finset.univ : Finset (Fin n))),
            ∏ i : Fin 2, g₀.inner x (e (J i)) (vec i) ^ 2 from by
        rw [Fintype.piFinset_univ]]
      rw [← Finset.prod_univ_sum (fun _ : Fin 2 => (Finset.univ : Finset (Fin n)))
        (fun i j => g₀.inner x (e j) (vec i) ^ 2)]
      rw [Fin.prod_univ_two]
      rw [hpars (vec 0), hpars (vec 1)]
      have h0 : vec 0 = a := rfl
      have h1 : vec 1 = b := rfl
      rw [h0, h1]
    rw [hKsum, hJsum]
  have hcompsq : (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), comp p ^ 2) =
      ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ^ 2 := by
    rw [← riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 1 2 x W]
    rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 1 2 x W e bse hnE hbse horth]
    rw [Fintype.sum_prod_type]
  have hnorm_nn : 0 ≤ ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ := norm_nonneg _
  have habs_sq : (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p) ^ 2 ≤
      ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ^ 2 *
        (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b)) := by
    calc (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p) ^ 2
        ≤ (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p ^ 2) *
            ∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), comp p ^ 2 := hCS
      _ = (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b)) *
            ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ^ 2 := by
            rw [hcoefsq, hcompsq]
      _ = ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ^ 2 *
            (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b)) := by ring
  rw [← Real.sqrt_sq (abs_nonneg (∑ p : (Fin 1 → Fin n) × (Fin 2 → Fin n), coef p * comp p)),
    sq_abs]
  rw [show ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ *
        Real.sqrt (g₀.inner x d d) *
        Real.sqrt (g₀.inner x a a) * Real.sqrt (g₀.inner x b b) =
      Real.sqrt (‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ^ 2 *
        (g₀.inner x d d * (g₀.inner x a a * g₀.inner x b b))) from ?_]
  · exact Real.sqrt_le_sqrt habs_sq
  · rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnorm_nn]
    rw [Real.sqrt_mul hdd_nn, Real.sqrt_mul haa_nn]
    ring

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
private theorem exists_fixed_connDiff_sqrt_bound (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v w : TangentSpace I x),
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g_bg g₀ x v w)
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x v w)) ≤
        C * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  classical
  obtain ⟨K, hK0, hK⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
    g₀ 1 2 (connDiffSection (I := I) g_bg g₀)
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, ?_⟩
  intro x v w
  letI instW : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 1 2 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 1 2
  set cd : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g_bg g₀ x v w with hcd_def
  set W : TensorRSSpace 1 2 I x := connDiffFib (I := I) g_bg g₀ x with hW_def
  have hval : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
        (g0FlatCLM (I := I) g₀ x cd)) (Fin.cons (v : E) ![(w : E)]) = g₀.inner x cd cd := by
    rw [show Tensor0SSpace.toModel ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W)
          (g0FlatCLM (I := I) g₀ x cd)) (Fin.cons (v : E) ![(w : E)]) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            connDiffFib (I := I) g_bg g₀ x)
          (g0FlatCLM (I := I) g₀ x cd)) ![v, w] from rfl]
    rw [connDiffFib_apply_eval (I := I) g_bg g₀ x (g0FlatCLM (I := I) g₀ x cd) ![v, w]]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show (g0FlatCLM (I := I) g₀ x cd)
          (fun _ : Fin 1 => PDE.DeTurck.connDiff (I := I) g_bg g₀ x v w) =
        cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x cd)
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x v w) from
      (cotangentToDual_apply (I := I) (x := x) _ _).symm]
    rw [cotangentToDual_g0FlatCLM (I := I) g₀ x cd]
  have habs := abs_tensor12_flat_eval_le_fibreNorm_mul_sqrt_local (I := I) (M := M)
    g₀ x W cd v w
  rw [hval] at habs
  have hcdcd_nn : 0 ≤ g₀.inner x cd cd := metric_inner_self_nonneg (I := I) (M := M) g₀ x cd
  rw [abs_of_nonneg hcdcd_nn] at habs
  have hWnorm : ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ≤ Real.sqrt K := by
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 2 x W ≤ K := by
      have h := hK x
      rw [connDiffSection_toSection] at h
      rw [hW_def]
      exact h
    have h1 : ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ^ 2 ≤ K := by
      rw [← riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 1 2 x W]
      exact h2
    calc ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖
        = Real.sqrt (‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt K := Real.sqrt_le_sqrt h1
  set NA : ℝ := Real.sqrt (g₀.inner x cd cd) with hNA_def
  have hNA_nn : 0 ≤ NA := Real.sqrt_nonneg _
  have hAA_sq : g₀.inner x cd cd = NA ^ 2 := by rw [hNA_def, Real.sq_sqrt hcdcd_nn]
  set Sv : ℝ := Real.sqrt (g₀.inner x v v) with hSv_def
  set Sw : ℝ := Real.sqrt (g₀.inner x w w) with hSw_def
  have hSv_nn : 0 ≤ Sv := Real.sqrt_nonneg _
  have hSw_nn : 0 ≤ Sw := Real.sqrt_nonneg _
  set NW : ℝ := ‖(W : Tensor0SBundle.TensorRSSpace 1 2 I x)‖ with hNW_def
  have hNW_nn : 0 ≤ NW := norm_nonneg _
  have hprim' : NA ^ 2 ≤ NW * NA * Sv * Sw := by
    rw [← hAA_sq]
    exact habs
  have hNA_le : NA ≤ NW * Sv * Sw := by
    rcases eq_or_lt_of_le hNA_nn with hNA0 | hNApos
    · rw [← hNA0]
      positivity
    · have hkey : NA * NA ≤ NA * (NW * Sv * Sw) := by
        rw [show NA * NA = NA ^ 2 from by ring]
        refine le_trans hprim' ?_
        apply le_of_eq; ring
      exact le_of_mul_le_mul_left hkey hNApos
  calc NA ≤ NW * Sv * Sw := hNA_le
    _ ≤ Real.sqrt K * Sv * Sw := by
        have hprod_nn : 0 ≤ Sv * Sw := mul_nonneg hSv_nn hSw_nn
        nlinarith [hWnorm, hprod_nn, hSv_nn, hSw_nn, hNW_nn]

omit [NeZero (Module.finrank ℝ E)] in
private theorem covGrad_connDiffSection_flat_eval_eq_inner_local
    (g₀ g_c : SmoothRiemannianMetric I M) (x : M) (v w u : TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_c g₀)).toSection x)
          (g0FlatCLM (I := I) g₀ x
            (covDerivConnDiff (I := I) g₀ g_c
              (smoothExtensionTangent (I := I) x v)
              (smoothExtensionTangent (I := I) x w)
              (smoothExtensionTangent (I := I) x u) x)))
        (Fin.cons v (Fin.cons u ![w])) =
      g₀.inner x
        (covDerivConnDiff (I := I) g₀ g_c
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x)
        (covDerivConnDiff (I := I) g₀ g_c
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w)
          (smoothExtensionTangent (I := I) x u) x) := by
  classical
  set A : TangentSpace I x :=
    covDerivConnDiff (I := I) g₀ g_c
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent (I := I) x u) x with hA_def
  set Xsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent_contMDiff (I := I) x v) with hXsec_def
  set Ysec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x u)
      (smoothExtensionTangent_contMDiff (I := I) x u) with hYsec_def
  set Zsec : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent_contMDiff (I := I) x w) with hZsec_def
  have hXx : Xsec x = v := smoothExtensionTangent_eq (I := I) x v
  have hYx : Ysec x = u := smoothExtensionTangent_eq (I := I) x u
  have hZx : Zsec x = w := smoothExtensionTangent_eq (I := I) x w
  have hA_bridge : covDerivConnDiff (I := I) g₀ g_c Xsec Zsec Ysec x = A := by
    rw [hA_def]; rfl
  obtain ⟨om, hom⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := Tensor0SModel 1 ℝ E) (V := fun y : M => Tensor0SSpace 1 I y) x
    (g0FlatCLM (I := I) g₀ x A)
  have hbridge := connDiffSection_covGrad_eq_covDerivConnDiff (I := I) g_c g₀ om Xsec Ysec Zsec x
  rw [hom, hXx, hYx, hZx, hA_bridge] at hbridge
  have hflatA : (g0FlatCLM (I := I) g₀ x A) (fun _ : Fin 1 => A) = g₀.inner x A A := by
    rw [show (g0FlatCLM (I := I) g₀ x A) (fun _ : Fin 1 => A) =
        cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x A) A from
      (cotangentToDual_apply (I := I) (x := x) _ _).symm]
    rw [cotangentToDual_g0FlatCLM (I := I) g₀ x A A]
  rw [hflatA] at hbridge
  rw [hA_def]
  exact hbridge

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
private theorem exists_fixed_covDerivConnDiff_sqrt_bound
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (v w u : TangentSpace I x),
      Real.sqrt (g₀.inner x
          (covDerivConnDiff (I := I) g₀ g_bg
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)
          (covDerivConnDiff (I := I) g₀ g_bg
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)) ≤
        C * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) *
          Real.sqrt (g₀.inner x u u) := by
  classical
  obtain ⟨K, hK0, hK⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M)
    g₀ 1 3 (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀))
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, ?_⟩
  intro x v w u
  letI instW : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 1 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 1 3
  set W : Tensor0SBundle.TensorRSSpace 1 3 I x :=
    (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀)).toSection x
    with hW_def
  set A : TangentSpace I x :=
    covDerivConnDiff (I := I) g₀ g_bg
      (smoothExtensionTangent (I := I) x v)
      (smoothExtensionTangent (I := I) x w)
      (smoothExtensionTangent (I := I) x u) x with hA_def
  have hAA_nn : 0 ≤ g₀.inner x A A := metric_inner_self_nonneg (I := I) (M := M) g₀ x A
  set NA : ℝ := Real.sqrt (g₀.inner x A A) with hNA_def
  have hNA_nn : 0 ≤ NA := Real.sqrt_nonneg _
  have hbridge := covGrad_connDiffSection_flat_eval_eq_inner_local (I := I) (M := M)
    g₀ g_bg x v w u
  rw [← hA_def, ← hW_def] at hbridge
  have hprim := abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt (I := I) (M := M) g₀ x W A v u w
  rw [hbridge] at hprim
  rw [abs_of_nonneg hAA_nn] at hprim
  have hAA_sq : g₀.inner x A A = NA ^ 2 := by rw [hNA_def, Real.sq_sqrt hAA_nn]
  set Sv : ℝ := Real.sqrt (g₀.inner x v v) with hSv_def
  set Sw : ℝ := Real.sqrt (g₀.inner x w w) with hSw_def
  set Su : ℝ := Real.sqrt (g₀.inner x u u) with hSu_def
  have hSv_nn : 0 ≤ Sv := Real.sqrt_nonneg _
  have hSw_nn : 0 ≤ Sw := Real.sqrt_nonneg _
  have hSu_nn : 0 ≤ Su := Real.sqrt_nonneg _
  set NW : ℝ := ‖(W : Tensor0SBundle.TensorRSSpace 1 3 I x)‖ with hNW_def
  have hNW_nn : 0 ≤ NW := norm_nonneg _
  have hWnorm : NW ≤ Real.sqrt K := by
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 3 x W ≤ K := hK x
    have h1 : NW ^ 2 ≤ K := by
      rw [hNW_def, ← riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 1 3 x W]
      exact h2
    calc NW = Real.sqrt (NW ^ 2) := (Real.sqrt_sq hNW_nn).symm
      _ ≤ Real.sqrt K := Real.sqrt_le_sqrt h1
  have hprim' : NA ^ 2 ≤ NW * NA * Sv * Su * Sw := by
    rw [← hAA_sq]
    exact hprim
  have hNA_le : NA ≤ NW * Sv * Sw * Su := by
    rcases eq_or_lt_of_le hNA_nn with hNA0 | hNApos
    · rw [← hNA0]
      positivity
    · have hkey : NA * NA ≤ NA * (NW * Sv * Su * Sw) := by
        rw [show NA * NA = NA ^ 2 from by ring]
        refine le_trans hprim' ?_
        apply le_of_eq; ring
      have hcancel := le_of_mul_le_mul_left hkey hNApos
      calc NA ≤ NW * Sv * Su * Sw := hcancel
        _ = NW * Sv * Sw * Su := by ring
  calc NA ≤ NW * Sv * Sw * Su := hNA_le
    _ ≤ Real.sqrt K * Sv * Sw * Su := by
        have hprod_nn : 0 ≤ Sv * Sw * Su := by positivity
        nlinarith [hWnorm, hprod_nn, hSv_nn, hSw_nn, hSu_nn, hNW_nn]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem deTurckLieDLaCoeffField_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
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
              ((deTurckLieConnDiffDerivCoeffField (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤ Λ := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  have hcoeff : 0 < 1 - δ₁ := by linarith
  set κ : ℝ := Real.sqrt (1 / (1 - δ₁)) with hκ_def
  have hκ_nn : 0 ≤ κ := Real.sqrt_nonneg _
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_Csob_convexPerturbation_pointwise_C2_le
      (I := I) (M := M) g₀ a ha_super
  set B : ℝ := Csob * R with hB_def
  have hB_nn : 0 ≤ B := mul_nonneg hCsob_nn hR
  obtain ⟨Cq, hCq_nn, hCq⟩ :=
    exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope (I := I) (M := M) g₀
      (δ₀ := δ₁) hδ₁_lt B hB_nn
  obtain ⟨Cbg, hCbg_nn, hCbg⟩ :=
    exists_fixed_covDerivConnDiff_sqrt_bound (I := I) (M := M) g₀ g_bg
  obtain ⟨Cc, hCc_nn, hCc⟩ := exists_fixed_connDiff_sqrt_bound (I := I) (M := M) g₀ g_bg
  obtain ⟨Ca0, hCa0_nn, hCa0⟩ :=
    connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one (I := I) (M := M) g₀ hδ₁_nn hδ₁_lt
  set CaB : ℝ := Ca0 * B with hCaB_def
  have hCaB_nn : 0 ≤ CaB := mul_nonneg hCa0_nn hB_nn
  set CK : ℝ := (Cq + Cbg + 3 * (CaB * (CaB + Cc))) * (κ * κ) with hCK_def
  have hCK_nn : 0 ≤ CK := by
    rw [hCK_def]
    refine mul_nonneg ?_ (mul_nonneg hκ_nn hκ_nn)
    have h3 : 0 ≤ CaB * (CaB + Cc) := mul_nonneg hCaB_nn (add_nonneg hCaB_nn hCc_nn)
    linarith [hCq_nn, hCbg_nn, h3]
  refine ⟨((Module.finrank ℝ E : ℝ) ^ 2) ^ 2 *
      ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ)))) ^ 2,
    by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  obtain ⟨hs0, hs1⟩ := hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ') :=
    abs_convex_smallConstant_lt_one hδ_lt hδ'_lt ⟨hs0, hs1⟩
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁
  set P : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s with hP_def
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w := by
    intro y v w
    rw [hg₁, hP_def]
    exact realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ' hs_mem y v w
  have hδs_raw : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
      (|1 - s| * δ' + |s| * δ) := by
    rw [hP_def]
    exact convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  set δP : ℝ := max (|1 - s| * δ' + |s| * δ) 0 with hδP_def
  have hδP_nn : 0 ≤ δP := le_max_right _ _
  have hδP_bound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δP :=
    gFibreOpBound_mono_of_le (I := I) (M := M) g₀ _ (le_max_left _ _) hδs_raw
  have hδP_le : δP ≤ δ₁ := by
    refine max_le ?_ hδ₁_nn
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s), abs_of_nonneg hs0]
    have h1 : δ' ≤ δ₁ := le_trans hδ'_le (le_max_left _ _)
    have h2 : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    nlinarith [h1, h2]
  have hδP_lt1 : δP < 1 := lt_of_le_of_lt hδP_le hδ₁_lt
  have henv := hCsob T T' hR hTball hT'ball s ⟨hs0, hs1⟩ x
  rw [← hP_def, ← hB_def] at henv
  letI inst03 : Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  set N1 : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 P).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hN1_def
  have hN1_le : N1 ≤ B := by
    have hterms : ∀ k ∈ Finset.range 3, (0 : ℝ) ≤
        (letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + k) I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
        ‖(iteratedCovGrad (I := I) g₀ 0 2 k P).toSection x‖) := by
      intro k _
      letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 (2 + k) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
      exact norm_nonneg _
    have h1 := Finset.single_le_sum hterms (by norm_num : (1:ℕ) ∈ Finset.range 3)
    have h2 := le_trans h1 henv
    rw [← hN1_def] at h2
    exact h2
  have hquad : ∀ v w u : TangentSpace I x,
      Real.sqrt (g₀.inner x
          (covDerivConnDiff (I := I) g₀ g₁
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)
          (covDerivConnDiff (I := I) g₀ g₁
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)) ≤
        Cq * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) *
          Real.sqrt (g₀.inner x u u) := by
    intro v w u
    exact hCq g₁ P (δ := δP) (le_trans hδP_le (le_max_left _ _)) hδP_bound htie x henv v w u
  have hconn_g1 : ∀ u v : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)) ≤
      CaB * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) := by
    intro u v
    have h := hCa0 g₁ P htie (δ := δP) hδP_le hδP_nn hδP_bound x u v
    rw [← hN1_def] at h
    refine le_trans h ?_
    have hsu : 0 ≤ Real.sqrt (g₀.inner x u u) := Real.sqrt_nonneg _
    have hsv : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
    have hN1_nn : 0 ≤ N1 := norm_nonneg _
    calc Ca0 * N1 * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)
        ≤ Ca0 * B * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
          have hmono : Ca0 * N1 ≤ Ca0 * B := mul_le_mul_of_nonneg_left hN1_le hCa0_nn
          have h1 : Ca0 * N1 * Real.sqrt (g₀.inner x u u) ≤
              Ca0 * B * Real.sqrt (g₀.inner x u u) :=
            mul_le_mul_of_nonneg_right hmono hsu
          exact mul_le_mul_of_nonneg_right h1 hsv
      _ = CaB * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) := by
          rw [hCaB_def]; ring
  have hcocy : ∀ u v : TangentSpace I x,
      PDE.DeTurck.connDiff (I := I) g₁ g_bg x u v =
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v -
          PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v :=
    fun u v => eq_sub_of_add_eq (connDiff_cocycle (I := I) g₁ g_bg g₀ x u v)
  have hconn_gbg : ∀ u v : TangentSpace I x,
      Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x u v)
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg x u v)) ≤
      (CaB + Cc) * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) := by
    intro u v
    rw [hcocy u v]
    refine le_trans (sqrt_metric_inner_sub_le (I := I) (M := M) g₀ x _ _) ?_
    have h1 := hconn_g1 u v
    have h2 := hCc x u v
    calc Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v))
          + Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v)
            (PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v))
        ≤ CaB * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v))
          + Cc * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := add_le_add h1 h2
      _ = (CaB + Cc) * (Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) := by ring
  have hpinch : ∀ a' : Fin (Module.finrank ℝ E),
      Real.sqrt (g₀.inner x (smoothOrthoFrame (I := I) g₁ x a' x)
        (smoothOrthoFrame (I := I) g₁ x a' x)) ≤ κ := by
    intro a'
    set Ba : TangentSpace I x := smoothOrthoFrame (I := I) g₁ x a' x with hBa
    have hg1BB : g₁.inner x Ba Ba = 1 := by
      have h := smoothOrthoFrame_orthonormal_at_center (I := I) g₁ x a' a'
      rw [if_pos rfl] at h
      exact h
    have hBB_nn : 0 ≤ g₀.inner x Ba Ba := metric_inner_self_nonneg (I := I) (M := M) g₀ x Ba
    have hsq : Real.sqrt (g₀.inner x Ba Ba) * Real.sqrt (g₀.inner x Ba Ba) =
        g₀.inner x Ba Ba := Real.mul_self_sqrt hBB_nn
    have hpert' : |ccTensorBilinSymm (I := I) g₀ P x Ba Ba| ≤ δP * g₀.inner x Ba Ba := by
      calc |ccTensorBilinSymm (I := I) g₀ P x Ba Ba|
          ≤ δP * Real.sqrt (g₀.inner x Ba Ba) * Real.sqrt (g₀.inner x Ba Ba) :=
            hδP_bound x Ba Ba
        _ = δP * g₀.inner x Ba Ba := by rw [mul_assoc, hsq]
    have htie' := htie x Ba Ba
    rw [hg1BB] at htie'
    have hlow : g₀.inner x Ba Ba - δP * g₀.inner x Ba Ba ≤ 1 := by
      have h1 := (abs_le.mp hpert').1
      linarith [htie'.symm]
    have hBB_le : g₀.inner x Ba Ba ≤ 1 / (1 - δ₁) := by
      have hδP1 : 1 - δ₁ ≤ 1 - δP := by linarith [hδP_le]
      have h2 : (1 - δP) * g₀.inner x Ba Ba ≤ 1 := by nlinarith [hlow]
      have h3 : (1 - δ₁) * g₀.inner x Ba Ba ≤ (1 - δP) * g₀.inner x Ba Ba :=
        mul_le_mul_of_nonneg_right hδP1 hBB_nn
      rw [le_div_iff₀ hcoeff]
      nlinarith [h2, h3]
    calc Real.sqrt (g₀.inner x Ba Ba) ≤ Real.sqrt (1 / (1 - δ₁)) := Real.sqrt_le_sqrt hBB_le
      _ = κ := by rw [hκ_def]
  have hkernel : ∀ (v0 : TangentSpace I x), g₀.inner x v0 v0 = 1 →
      ∀ a' b' : Fin (Module.finrank ℝ E),
      Real.sqrt (g₀.inner x
        (connDiffCovDerivOp (I := I) g₁ g_bg x v0 (smoothOrthoFrame (I := I) g₁ x a' x)
          (smoothOrthoFrame (I := I) g₁ x b' x))
        (connDiffCovDerivOp (I := I) g₁ g_bg x v0 (smoothOrthoFrame (I := I) g₁ x a' x)
          (smoothOrthoFrame (I := I) g₁ x b' x))) ≤ CK := by
    intro v0 hv0 a' b'
    set Ba : TangentSpace I x := smoothOrthoFrame (I := I) g₁ x a' x with hBa
    set Bb : TangentSpace I x := smoothOrthoFrame (I := I) g₁ x b' x with hBb
    have hBa_le : Real.sqrt (g₀.inner x Ba Ba) ≤ κ := hpinch a'
    have hBb_le : Real.sqrt (g₀.inner x Bb Bb) ≤ κ := hpinch b'
    have hBa_nn : 0 ≤ Real.sqrt (g₀.inner x Ba Ba) := Real.sqrt_nonneg _
    have hBb_nn : 0 ≤ Real.sqrt (g₀.inner x Bb Bb) := Real.sqrt_nonneg _
    have hv0_sqrt : Real.sqrt (g₀.inner x v0 v0) = 1 := by rw [hv0, Real.sqrt_one]
    rw [dLaCovKernel_backgroundSplit (I := I) g₀ g₁ g_bg x v0 Ba Bb]
    set A1 : TangentSpace I x := covDerivConnDiff (I := I) g₀ g₁
      (smoothExtensionTangent (I := I) x v0)
      (smoothExtensionTangent (I := I) x Bb)
      (smoothExtensionTangent (I := I) x Ba) x with hA1
    set A2 : TangentSpace I x := covDerivConnDiff (I := I) g₀ g_bg
      (smoothExtensionTangent (I := I) x v0)
      (smoothExtensionTangent (I := I) x Bb)
      (smoothExtensionTangent (I := I) x Ba) x with hA2
    set Q1 : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      (PDE.DeTurck.connDiff (I := I) g₁ g_bg x Ba Bb) v0 with hQ1
    set Q2 : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g_bg x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0) Bb with hQ2
    set Q3 : TangentSpace I x := PDE.DeTurck.connDiff (I := I) g₁ g_bg x Ba
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0) with hQ3
    have t1 := sqrt_metric_inner_sub_le (I := I) (M := M) g₀ x (A1 - A2 + Q1 - Q2) Q3
    have t2 := sqrt_metric_inner_sub_le (I := I) (M := M) g₀ x (A1 - A2 + Q1) Q2
    have t3 := sqrt_metric_inner_add_le (I := I) (M := M) g₀ x (A1 - A2) Q1
    have t4 := sqrt_metric_inner_sub_le (I := I) (M := M) g₀ x A1 A2
    have hA1_le : Real.sqrt (g₀.inner x A1 A1) ≤ Cq * (κ * κ) := by
      have h := hquad v0 Bb Ba
      rw [hv0_sqrt] at h
      refine le_trans h ?_
      calc Cq * 1 * Real.sqrt (g₀.inner x Bb Bb) * Real.sqrt (g₀.inner x Ba Ba)
          ≤ Cq * 1 * κ * κ := by
            have h1 : Cq * 1 * Real.sqrt (g₀.inner x Bb Bb) ≤ Cq * 1 * κ :=
              mul_le_mul_of_nonneg_left hBb_le (by linarith [hCq_nn])
            have h2 : Cq * 1 * Real.sqrt (g₀.inner x Bb Bb) * Real.sqrt (g₀.inner x Ba Ba) ≤
                Cq * 1 * κ * Real.sqrt (g₀.inner x Ba Ba) :=
              mul_le_mul_of_nonneg_right h1 hBa_nn
            refine le_trans h2 ?_
            exact mul_le_mul_of_nonneg_left hBa_le (by positivity)
        _ = Cq * (κ * κ) := by ring
    have hA2_le : Real.sqrt (g₀.inner x A2 A2) ≤ Cbg * (κ * κ) := by
      have h := hCbg x v0 Bb Ba
      rw [hv0_sqrt] at h
      refine le_trans h ?_
      calc Cbg * 1 * Real.sqrt (g₀.inner x Bb Bb) * Real.sqrt (g₀.inner x Ba Ba)
          ≤ Cbg * 1 * κ * κ := by
            have h1 : Cbg * 1 * Real.sqrt (g₀.inner x Bb Bb) ≤ Cbg * 1 * κ :=
              mul_le_mul_of_nonneg_left hBb_le (by linarith [hCbg_nn])
            have h2 : Cbg * 1 * Real.sqrt (g₀.inner x Bb Bb) * Real.sqrt (g₀.inner x Ba Ba) ≤
                Cbg * 1 * κ * Real.sqrt (g₀.inner x Ba Ba) :=
              mul_le_mul_of_nonneg_right h1 hBa_nn
            refine le_trans h2 ?_
            exact mul_le_mul_of_nonneg_left hBa_le (by positivity)
        _ = Cbg * (κ * κ) := by ring
    have hin_bg : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g_bg x Ba Bb)
        (PDE.DeTurck.connDiff (I := I) g₁ g_bg x Ba Bb)) ≤ (CaB + Cc) * (κ * κ) := by
      refine le_trans (hconn_gbg Ba Bb) ?_
      have hmul : Real.sqrt (g₀.inner x Ba Ba) * Real.sqrt (g₀.inner x Bb Bb) ≤ κ * κ := by
        have h1 : Real.sqrt (g₀.inner x Ba Ba) * Real.sqrt (g₀.inner x Bb Bb) ≤
            κ * Real.sqrt (g₀.inner x Bb Bb) := mul_le_mul_of_nonneg_right hBa_le hBb_nn
        refine le_trans h1 ?_
        exact mul_le_mul_of_nonneg_left hBb_le hκ_nn
      exact mul_le_mul_of_nonneg_left hmul (add_nonneg hCaB_nn hCc_nn)
    have hQ1_le : Real.sqrt (g₀.inner x Q1 Q1) ≤ CaB * ((CaB + Cc) * (κ * κ)) := by
      have h := hconn_g1 (PDE.DeTurck.connDiff (I := I) g₁ g_bg x Ba Bb) v0
      rw [hv0_sqrt, mul_one] at h
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_left hin_bg hCaB_nn
    have hin2 : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)) ≤ CaB * κ := by
      have h := hconn_g1 Ba v0
      rw [hv0_sqrt, mul_one] at h
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_left hBa_le hCaB_nn
    have hQ2_le : Real.sqrt (g₀.inner x Q2 Q2) ≤ (CaB + Cc) * (CaB * (κ * κ)) := by
      have h := hconn_gbg (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0) Bb
      refine le_trans h ?_
      have hmul : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)) * Real.sqrt (g₀.inner x Bb Bb) ≤
          (CaB * κ) * κ := by
        have h1 : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Ba v0)) * Real.sqrt (g₀.inner x Bb Bb) ≤
            (CaB * κ) * Real.sqrt (g₀.inner x Bb Bb) := mul_le_mul_of_nonneg_right hin2 hBb_nn
        refine le_trans h1 ?_
        exact mul_le_mul_of_nonneg_left hBb_le (by positivity)
      refine le_trans (mul_le_mul_of_nonneg_left hmul (add_nonneg hCaB_nn hCc_nn)) ?_
      apply le_of_eq
      ring
    have hin3 : Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)) ≤ CaB * κ := by
      have h := hconn_g1 Bb v0
      rw [hv0_sqrt, mul_one] at h
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_left hBb_le hCaB_nn
    have hQ3_le : Real.sqrt (g₀.inner x Q3 Q3) ≤ (CaB + Cc) * (CaB * (κ * κ)) := by
      have h := hconn_gbg Ba (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)
      refine le_trans h ?_
      have hmul : Real.sqrt (g₀.inner x Ba Ba) *
          Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)) ≤ κ * (CaB * κ) := by
        have h1 : Real.sqrt (g₀.inner x Ba Ba) *
            Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)) ≤
            κ * Real.sqrt (g₀.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)
              (PDE.DeTurck.connDiff (I := I) g₁ g₀ x Bb v0)) :=
          mul_le_mul_of_nonneg_right hBa_le (Real.sqrt_nonneg _)
        refine le_trans h1 ?_
        exact mul_le_mul_of_nonneg_left hin3 hκ_nn
      refine le_trans (mul_le_mul_of_nonneg_left hmul (add_nonneg hCaB_nn hCc_nn)) ?_
      apply le_of_eq
      ring
    have hchain : Real.sqrt (g₀.inner x (A1 - A2 + Q1 - Q2 - Q3) (A1 - A2 + Q1 - Q2 - Q3)) ≤
        Real.sqrt (g₀.inner x A1 A1) + Real.sqrt (g₀.inner x A2 A2) +
          Real.sqrt (g₀.inner x Q1 Q1) + Real.sqrt (g₀.inner x Q2 Q2) +
          Real.sqrt (g₀.inner x Q3 Q3) := by
      refine le_trans t1 ?_
      have s2 := le_trans t2 (by linarith [t3, t4] :
        Real.sqrt (g₀.inner x (A1 - A2 + Q1) (A1 - A2 + Q1)) +
            Real.sqrt (g₀.inner x Q2 Q2) ≤
          Real.sqrt (g₀.inner x A1 A1) + Real.sqrt (g₀.inner x A2 A2) +
            Real.sqrt (g₀.inner x Q1 Q1) + Real.sqrt (g₀.inner x Q2 Q2))
      linarith [s2]
    refine le_trans hchain ?_
    rw [hCK_def]
    nlinarith [hA1_le, hA2_le, hQ1_le, hQ2_le, hQ3_le]
  obtain ⟨n, e, bse, hn, hbse, horth, hpars, hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := hn
  have hunit : ∀ i : Fin n, g₀.inner x (e i) (e i) = 1 := by
    intro i
    have h := horth i i
    rw [if_pos rfl] at h
    exact h
  have hunit_sqrt : ∀ i : Fin n, Real.sqrt (g₀.inner x (e i) (e i)) = 1 := by
    intro i
    rw [hunit i, Real.sqrt_one]
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 2 2 x
    ((deTurckLieConnDiffDerivCoeffField (I := I) g₀ g₁ g_bg).toSection x) e bse hnE hbse horth]
  have heach : ∀ (K : Fin 2 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        ((deTurckLieConnDiffDerivCoeffField (I := I) g₀ g₁ g_bg).toSection x) n e K J) ^ 2 ≤
      ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ)))) ^ 2 := by
    intro K J
    have hcomp_eq : fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        ((deTurckLieConnDiffDerivCoeffField (I := I) g₀ g₁ g_bg).toSection x) n e K J =
      Tensor0SSpace.toModel
        ((connDiffCovDerivBiContrFib (I := I) g₁ g_bg x) (coframeS (I := I) (M := M) g₀ x 2 e K))
        (fun i : Fin 2 => (e (J i) : E)) := rfl
    have hmodel : Tensor0SSpace.toModel
        ((connDiffCovDerivBiContrFib (I := I) g₁ g_bg x) (coframeS (I := I) (M := M) g₀ x 2 e K))
        (fun i : Fin 2 => (e (J i) : E)) =
      (-1 : ℝ) * ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
        (g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
            (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
            (e (J 1))
          + g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
            (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
            (e (J 0))) *
          Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
            ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
              (smoothOrthoFrame (I := I) g₁ x b' x : E)] :=
      dLaBiContrFibFixedFrame_toModel (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x) x
        (coframeS (I := I) (M := M) g₀ x 2 e K) (fun i : Fin 2 => (e (J i) : E))
    have hsingle : ∀ a' b' : Fin (Module.finrank ℝ E),
        |(g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
            (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
            (e (J 1))
          + g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
            (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
            (e (J 0))) *
          Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
            ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
              (smoothOrthoFrame (I := I) g₁ x b' x : E)]| ≤ 4 * CK * (κ * κ) := by
      intro a' b'
      rw [abs_mul]
      have hK01 : |g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
          (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
          (e (J 1))| ≤ 2 * CK := by
        refine le_trans (abs_g1_inner_le_two_sqrt (I := I) (M := M) g₀ g₁ P htie
          (le_of_lt hδP_lt1) hδP_bound x _ _) ?_
        rw [hunit_sqrt (J 1), mul_one]
        have h := hkernel (e (J 0)) (hunit (J 0)) a' b'
        linarith
      have hK10 : |g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
          (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
          (e (J 0))| ≤ 2 * CK := by
        refine le_trans (abs_g1_inner_le_two_sqrt (I := I) (M := M) g₀ g₁ P htie
          (le_of_lt hδP_lt1) hδP_bound x _ _) ?_
        rw [hunit_sqrt (J 0), mul_one]
        have h := hkernel (e (J 1)) (hunit (J 1)) a' b'
        linarith
      have hfac1 : |g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
          (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
          (e (J 1))
          + g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
            (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
            (e (J 0))| ≤ 4 * CK := by
        refine le_trans (abs_add_le _ _) ?_
        linarith [hK01, hK10]
      have hfac2 : |Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
          ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
            (smoothOrthoFrame (I := I) g₁ x b' x : E)]| ≤ κ * κ := by
        rw [toModel_coframeS_two (I := I) (M := M) g₀ x e K _ _]
        rw [abs_mul]
        have hcs1 : |g₀.inner x (e (K 0)) (smoothOrthoFrame (I := I) g₁ x a' x)| ≤ κ := by
          refine le_trans (abs_metric_inner_le (I := I) (M := M) g₀ x _ _) ?_
          rw [hunit_sqrt (K 0), one_mul]
          exact hpinch a'
        have hcs2 : |g₀.inner x (e (K 1)) (smoothOrthoFrame (I := I) g₁ x b' x)| ≤ κ := by
          refine le_trans (abs_metric_inner_le (I := I) (M := M) g₀ x _ _) ?_
          rw [hunit_sqrt (K 1), one_mul]
          exact hpinch b'
        exact mul_le_mul hcs1 hcs2 (abs_nonneg _) hκ_nn
      calc |g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
            (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
            (e (J 1))
            + g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
              (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
              (e (J 0))| *
          |Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
            ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
              (smoothOrthoFrame (I := I) g₁ x b' x : E)]|
          ≤ (4 * CK) * (κ * κ) := by
            refine mul_le_mul hfac1 hfac2 (abs_nonneg _) ?_
            linarith [hCK_nn]
        _ = 4 * CK * (κ * κ) := by ring
    have habs_comp : |fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
        ((deTurckLieConnDiffDerivCoeffField (I := I) g₀ g₁ g_bg).toSection x) n e K J| ≤
        (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ))) := by
      rw [hcomp_eq, hmodel, neg_one_mul, abs_neg]
      calc |∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
            (g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
                (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
                (e (J 1))
              + g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
                (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
                (e (J 0))) *
              Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
                ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
                  (smoothOrthoFrame (I := I) g₁ x b' x : E)]|
          ≤ ∑ a' : Fin (Module.finrank ℝ E), |∑ b' : Fin (Module.finrank ℝ E),
            (g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
                (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
                (e (J 1))
              + g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
                (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
                (e (J 0))) *
              Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
                ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
                  (smoothOrthoFrame (I := I) g₁ x b' x : E)]| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
            |(g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 0))
                (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
                (e (J 1))
              + g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (e (J 1))
                (smoothOrthoFrame (I := I) g₁ x a' x) (smoothOrthoFrame (I := I) g₁ x b' x))
                (e (J 0))) *
              Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 2 e K)
                ![(smoothOrthoFrame (I := I) g₁ x a' x : E),
                  (smoothOrthoFrame (I := I) g₁ x b' x : E)]| :=
            Finset.sum_le_sum (fun a' _ => Finset.abs_sum_le_sum_abs _ _)
        _ ≤ ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
              (4 * CK * (κ * κ)) :=
            Finset.sum_le_sum (fun a' _ => Finset.sum_le_sum (fun b' _ => hsingle a' b'))
        _ = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ))) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs_comp 2
  calc ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 2 2
          ((deTurckLieConnDiffDerivCoeffField (I := I) g₀ g₁ g_bg).toSection x) n e K J) ^ 2
      ≤ ∑ K : Fin 2 → Fin n, ∑ J : Fin 2 → Fin n,
          ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ)))) ^ 2 :=
        Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun J _ => heach K J))
    _ = ((Module.finrank ℝ E : ℝ) ^ 2) ^ 2 *
        ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (4 * CK * (κ * κ)))) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
          Fintype.card_fin]
        rw [hnE]
        push_cast
        ring

end DifferentialGeometry.Integral.Connection

end
