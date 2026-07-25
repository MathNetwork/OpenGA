import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalCometricExtraction
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckPrincipalArmSpectralGarding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricInverseDifferenceMultiplier
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ConnLapCommutatorCoefficientTame
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingSharpC0JetSum
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.ChartH2GardingConstant
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2Weitzenbock
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomFieldActionIteratedCovGradWindow
import DifferentialGeometry.Analysis.Integration.L2.FiniteProductHolderFiberNorm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CometricPathResolventFactorization
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.IntegratedOrder2WeitzenbockRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.PointwiseTensorCurvatureRS
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.HomFieldCurvatureJetDecomposition


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

section

open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_g1_inner_injective (g₁ : SmoothRiemannianMetric I M) (x : M)
    {a b : TangentSpace I x} (hab : ∀ u : TangentSpace I x, g₁.inner x a u = g₁.inner x b u) :
    a = b := by
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g₁.pos x (a - b) hsub
  have hzero : g₁.inner x (a - b) (a - b) = 0 := by
    have hsplit : g₁.inner x (a - b) (a - b)
        = g₁.inner x (a - b) a - g₁.inner x (a - b) b := by rw [← map_sub]
    rw [hsplit, g₁.symm x (a - b) a, g₁.symm x (a - b) b, hab (a - b)]
    ring
  exact absurd hzero (ne_of_gt hpos)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_cometricLmodel_covectorOfCLM_inner_loc
    (g₁ : SmoothRiemannianMetric I M) (y : M)
    (φ : E →L[ℝ] ℝ) (u : TangentSpace I y) :
    g₁.inner y (cometricLmodel (I := I) g₁ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) u = φ (u : E) := by
  have h1 : cometricLmodel (I := I) g₁ y
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ) =
      inverseMetricSharpFib (I := I) g₁ y
        ((Tensor0SBundle.tensor0SSpace_continuousLinearEquiv (𝕜 := ℝ) (I := I) 1 y).symm
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)) := rfl
  rw [h1, inverseMetricSharpFib_inner (I := I) g₁ y _ u, cotangentToDualLinear_apply,
    cotangentToDual_apply]
  change (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E) φ)
      (fun _ : Fin 1 => (u : E)) = φ (u : E)
  rw [Tensor0SBundle.model_covectorOfCLM_apply]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma kscr_cometricLmodel_covOf_g0flat_eq (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((g₀.inner x v).toLinearMap.toContinuousLinearMap)) = v := by
  apply kscr_g1_inner_injective (I := I) g₀ x
  intro u
  rw [kscr_cometricLmodel_covectorOfCLM_inner_loc (I := I) g₀ x
    ((g₀.inner x v).toLinearMap.toContinuousLinearMap) u]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma kscr_flatRecon_eq_basisVec (g₀ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (b : Fin n) :
    ∑ k : Fin (Module.finrank ℝ E),
        (g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
          cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k)) = e b := by
  classical
  have hsmul : ∀ k : Fin (Module.finrank ℝ E),
      (g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
          cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((Module.finBasis ℝ E).cDualBasis k))
        = cometricLmodel (I := I) g₀ x
            (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
              ((g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
                ((Module.finBasis ℝ E).cDualBasis k))) := by
    intro k
    rw [map_smul, map_smul]
  rw [Finset.sum_congr rfl (fun k _ => hsmul k)]
  rw [← map_sum, ← map_sum]
  have hcoe : ∀ k : Fin (Module.finrank ℝ E),
      ((Module.finBasis ℝ E).cDualBasis k)
        = LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord k) := by
    intro k
    rw [Module.Basis.cDualBasis, Module.Basis.map_apply]
    congr 1
    exact congrFun (Module.Basis.coe_dualBasis (Module.finBasis ℝ E)) k
  have hsum : (∑ k : Fin (Module.finrank ℝ E),
        (g₀.inner x (e b) ((Module.finBasis ℝ E) k) : ℝ) •
          ((Module.finBasis ℝ E).cDualBasis k))
      = (g₀.inner x (e b)).toLinearMap.toContinuousLinearMap := by
    have hrepr := cdual_sum_repr (Module.finBasis ℝ E)
      ((g₀.inner x (e b)).toLinearMap.toContinuousLinearMap)
    refine Eq.trans ?_ hrepr
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hcoe k]
    congr 1
  rw [hsum]
  exact kscr_cometricLmodel_covOf_g0flat_eq (I := I) g₀ x (e b)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma kscr_deTurckCoeff_toModel_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (w : Tensor0SSpace 4 I x) (m : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) w) m =
      ∑ k : Fin (Module.finrank ℝ E),
        (Tensor0SSpace.toModel w)
          (Fin.cons
            ((metricComparisonDiffEndo (I := I) g₀ g₁ x
              (cometricLmodel (I := I) g₀ x
                (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
                  ((Module.finBasis ℝ E).cDualBasis k))) : TangentSpace I x) : E)
            (Fin.cons (((Module.finBasis ℝ E) k : E)) m)) := by
  classical
  rw [deTurckPrincipalCometricCoeff_toSection_clm_eq (I := I) (M := M) g₀ g₁ x,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply,
    cometricDoubleTraceFib_toModel, cometricDoubleTraceFib_toModel,
    modelDoubleTrace_apply, modelDoubleTrace_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  set wm : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ := Tensor0SSpace.toModel w with hwm
  set tail : Fin 3 → E := Fin.cons (((Module.finBasis ℝ E) k : E)) m with htail
  have hcurry : ∀ z : TangentSpace I x,
      wm (Fin.cons ((z : E)) tail)
        = ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => E) ℝ) wm
            ((z : TangentSpace I x) : E)) tail := by
    intro z; rw [continuousMultilinearCurryLeftEquiv_apply]
  rw [hcurry (cometricLmodel (I := I) g₁ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))),
    hcurry (cometricLmodel (I := I) g₀ x
        (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
          ((Module.finBasis ℝ E).cDualBasis k))),
    hcurry (metricComparisonDiffEndo (I := I) g₀ g₁ x
        (cometricLmodel (I := I) g₀ x
          (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
            ((Module.finBasis ℝ E).cDualBasis k))))]
  rw [← ContinuousMultilinearMap.sub_apply, ← map_sub]
  congr 2
  rw [cometricLmodel_sub_eq_gInvDiffRaisedEndo (I := I) g₀ g₁ x
    ((Module.finBasis ℝ E).cDualBasis k)]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma kscr_deTurckCoeff_component_eq (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x)
    (horth : ∀ i j : Fin n, g₀.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (K : Fin 4 → Fin n) (J : Fin 2 → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) n e K J =
      g₀.inner x (e (K 0)) (metricComparisonDiffEndo (I := I) g₀ g₁ x (e (K 1))) *
        ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
  classical
  have hcomp : fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
        (show TensorRSSpace 4 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x) n e K J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁).toSection x)
          (coframeS (I := I) (M := M) g₀ x 4 e K))
        (fun k => ((e (J k) : TangentSpace I x) : E)) := rfl
  rw [hcomp, kscr_deTurckCoeff_toModel_eq (I := I) (M := M) g₀ g₁ x
    (coframeS (I := I) (M := M) g₀ x 4 e K) (fun k => ((e (J k) : TangentSpace I x) : E))]
  set Rk : Fin (Module.finrank ℝ E) → TangentSpace I x := fun k =>
    cometricLmodel (I := I) g₀ x
      (Tensor0SBundle.model_covectorOfCLM (𝕜 := ℝ) (E := E)
        ((Module.finBasis ℝ E).cDualBasis k)) with hRk
  set Λ : TangentSpace I x →L[ℝ] TangentSpace I x :=
    metricComparisonDiffEndo (I := I) g₀ g₁ x with hΛ
  have hk : ∀ k : Fin (Module.finrank ℝ E),
      (Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K))
          (Fin.cons ((Λ (Rk k) : TangentSpace I x) : E)
            (Fin.cons (((Module.finBasis ℝ E) k : E))
              (fun j => ((e (J j) : TangentSpace I x) : E))))
        = g₀.inner x (e (K 0)) (Λ (Rk k))
          * g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k)
          * ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
    intro k
    have hcf : (Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 4 e K))
          (Fin.cons ((Λ (Rk k) : TangentSpace I x) : E)
            (Fin.cons (((Module.finBasis ℝ E) k : E))
              (fun j => ((e (J j) : TangentSpace I x) : E))))
        = coframeS (I := I) (M := M) g₀ x 4 e K
            (Fin.cons ((Λ (Rk k)) : TangentSpace I x)
              (Fin.cons (((Module.finBasis ℝ E) k : TangentSpace I x))
                (fun j => (e (J j) : TangentSpace I x)))) := rfl
    rw [hcf, coframeS_apply, Fin.prod_univ_four]
    change g₀.inner x (e (K 0)) (Λ (Rk k))
          * g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k)
          * g₀.inner x (e (K 2)) (e (J 0))
          * g₀.inner x (e (K 3)) (e (J 1))
        = _
    rw [horth (K 2) (J 0), horth (K 3) (J 1)]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hk k)]
  rw [← Finset.sum_mul]
  congr 1
  have hpull : g₀.inner x (e (K 0)) (Λ
          (∑ k : Fin (Module.finrank ℝ E),
            (g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) : ℝ) • Rk k))
      = ∑ k : Fin (Module.finrank ℝ E),
          g₀.inner x (e (K 0)) (Λ (Rk k)) * g₀.inner x (e (K 1)) ((Module.finBasis ℝ E) k) := by
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  rw [← hpull, kscr_flatRecon_eq_basisVec (I := I) g₀ x e (K 1)]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_sum_pi_fin_succ {n : ℕ} {β : Type*} [AddCommMonoid β]
    {N : ℕ} (g : (Fin (N + 1) → Fin n) → β) :
    (∑ p : Fin (N + 1) → Fin n, g p)
      = ∑ a : Fin n, ∑ q : Fin N → Fin n, g (Fin.cons a q) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (N + 1) => Fin n)).sum_comp g]
  rw [Fintype.sum_prod_type]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_deTurckCoeff_componentSqSum_eq (n : ℕ) (f : Fin n → Fin n → ℝ) :
    (∑ K : Fin 4 → Fin n, ∑ J : Fin 2 → Fin n,
      (f (K 0) (K 1) *
        ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2)
      = (n : ℝ) ^ 2 * ∑ a : Fin n, ∑ b : Fin n, (f a b) ^ 2 := by
  classical
  have hJcollapse : ∀ K : Fin 4 → Fin n,
      (∑ J : Fin 2 → Fin n,
        (f (K 0) (K 1) *
          ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2)
        = (f (K 0) (K 1)) ^ 2 := by
    intro K
    have hsplit : ∀ J : Fin 2 → Fin n,
        (f (K 0) (K 1) *
          ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2
          = (f (K 0) (K 1)) ^ 2 *
              ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0)) := by
      intro J
      by_cases h2 : K 2 = J 0 <;> by_cases h3 : K 3 = J 1 <;>
        simp [h2, h3]
    rw [Finset.sum_congr rfl (fun J _ => hsplit J), ← Finset.mul_sum]
    rw [kscr_sum_pi_fin_succ (fun J : Fin 2 → Fin n =>
      (if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))]
    have hinner : ∀ a : Fin n, (∑ q : Fin 1 → Fin n,
        (if K 2 = (Fin.cons a q : Fin 2 → Fin n) 0 then (1 : ℝ) else 0) *
          (if K 3 = (Fin.cons a q : Fin 2 → Fin n) 1 then (1 : ℝ) else 0))
        = (if K 2 = a then (1 : ℝ) else 0) := by
      intro a
      rw [kscr_sum_pi_fin_succ (fun q : Fin 1 → Fin n =>
        (if K 2 = (Fin.cons a q : Fin 2 → Fin n) 0 then (1 : ℝ) else 0) *
          (if K 3 = (Fin.cons a q : Fin 2 → Fin n) 1 then (1 : ℝ) else 0))]
      have hb : ∀ b : Fin n, (∑ _r : Fin 0 → Fin n,
          (if K 2 = (Fin.cons a (Fin.cons b (_r : Fin 0 → Fin n)) : Fin 2 → Fin n) 0
            then (1 : ℝ) else 0) *
            (if K 3 = (Fin.cons a (Fin.cons b (_r : Fin 0 → Fin n)) : Fin 2 → Fin n) 1
              then (1 : ℝ) else 0))
          = (if K 2 = a then (1 : ℝ) else 0) * (if K 3 = b then (1 : ℝ) else 0) := by
        intro b
        have hbody : ∀ r : Fin 0 → Fin n,
            (if K 2 = (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 0 then (1 : ℝ) else 0) *
              (if K 3 = (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 1 then (1 : ℝ) else 0)
            = (if K 2 = a then (1 : ℝ) else 0) * (if K 3 = b then (1 : ℝ) else 0) := by
          intro r
          rw [show (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 0 = a from rfl,
            show (Fin.cons a (Fin.cons b r) : Fin 2 → Fin n) 1 = b from rfl]
        rw [Finset.sum_congr rfl (fun r _ => hbody r), Finset.sum_const, Finset.card_univ]
        simp only [Fintype.card_fun, Fintype.card_fin, pow_zero, one_smul]
      rw [Finset.sum_congr rfl (fun b _ => hb b), ← Finset.mul_sum]
      rw [Finset.sum_ite_eq Finset.univ (K 3) (fun _ => (1 : ℝ))]
      simp
    rw [Finset.sum_congr rfl (fun a _ => hinner a)]
    rw [Finset.sum_ite_eq Finset.univ (K 2) (fun _ => (1 : ℝ))]
    simp
  rw [Finset.sum_congr rfl (fun K _ => hJcollapse K)]
  rw [kscr_sum_pi_fin_succ (fun K : Fin 4 → Fin n => (f (K 0) (K 1)) ^ 2)]
  have hstep : ∀ a : Fin n, (∑ q : Fin 3 → Fin n,
      (f ((Fin.cons a q : Fin 4 → Fin n) 0) ((Fin.cons a q : Fin 4 → Fin n) 1)) ^ 2)
      = (n : ℝ) ^ 2 * ∑ b : Fin n, (f a b) ^ 2 := by
    intro a
    rw [kscr_sum_pi_fin_succ (fun q : Fin 3 → Fin n =>
      (f ((Fin.cons a q : Fin 4 → Fin n) 0) ((Fin.cons a q : Fin 4 → Fin n) 1)) ^ 2)]
    have hb : ∀ b : Fin n, (∑ r : Fin 2 → Fin n,
        (f ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 0)
          ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 1)) ^ 2)
        = (n : ℝ) ^ 2 * (f a b) ^ 2 := by
      intro b
      have hval : ∀ r : Fin 2 → Fin n,
          (f ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 0)
            ((Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 1)) ^ 2 = (f a b) ^ 2 := by
        intro r
        rw [show (Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 0 = a from rfl,
          show (Fin.cons a (Fin.cons b r) : Fin 4 → Fin n) 1 = b from rfl]
      rw [Finset.sum_congr rfl (fun r _ => hval r), Finset.sum_const, Finset.card_univ]
      simp only [Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun b _ => hb b), ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun a _ => hstep a), ← Finset.mul_sum]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_deTurckPrincipalCometricCoeff_sub_le (g₀ ga gb : SmoothRiemannianMetric I M)
    (ha hb : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie_a : ∀ (y : M) (v w : TangentSpace I y),
      ga.inner y v w = g₀.inner y v w + ha y v w)
    (htie_b : ∀ (y : M) (v w : TangentSpace I y),
      gb.inner y v w = g₀.inner y v w + hb y v w)
    {δa δb δab : ℝ} (hδa_lt : δa < 1)
    (hδa : metricCauchySchwarzBound (I := I) (M := M) g₀ ha δa)
    (hδb_lt : δb < 1) (hδb_nn : 0 ≤ δb)
    (hδb : metricCauchySchwarzBound (I := I) (M := M) g₀ hb δb)
    (hδab_nn : 0 ≤ δab)
    (hδab : metricCauchySchwarzBound (I := I) (M := M) g₀ (fun y => ha y - hb y) δab)
    (_hδa_nn : 0 ≤ δa)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
        ((deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga
          - deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 * (δab / ((1 - δa) * (1 - δb))) ^ 2 := by
  classical
  set Λ : TangentSpace I x →L[ℝ] TangentSpace I x :=
    metricComparisonDiffEndo (I := I) g₀ ga x - metricComparisonDiffEndo (I := I) g₀ gb x with hΛ
  obtain ⟨n, e, hn, horth, hpar, hrepr⟩ :=
    exists_orthonormal_frame_riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
  have hnE : (n : ℝ) = (Module.finrank ℝ E : ℝ) := by rw [hn]; rfl
  have hsec : (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga
        - deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x =
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
        - (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  rw [hsec]
  rw [riemannianFiberNormSq_eq_sum_componentRS_sq (I := I) (M := M) g₀ x 4 2 e hrepr
    (show TensorRSSpace 4 2 I x from
      (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
        - (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x)]
  have hcompsub : ∀ (K : Fin 4 → Fin n) (J : Fin 2 → Fin n),
      fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
              - (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x) n e K J =
        fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x) n e K J
        - fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x) n e K J := by
    intro K J
    rw [show ((deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
          - (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x :
            TensorRSSpace 4 2 I x)
        = (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
          + (-1 : ℝ) • (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x from
      by rw [neg_one_smul]; exact sub_eq_add_neg _ _]
    rw [fiberNormSqComponent_add, fiberNormSqComponent_smul]
    ring
  have hcompsq : ∀ (K : Fin 4 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 4 2
          (show TensorRSSpace 4 2 I x from
            (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ ga).toSection x
              - (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ gb).toSection x)
          n e K J) ^ 2
        = (g₀.inner x (e (K 0)) (Λ (e (K 1))) *
            ((if K 2 = J 0 then (1 : ℝ) else 0) * (if K 3 = J 1 then (1 : ℝ) else 0))) ^ 2 := by
    intro K J
    rw [hcompsub K J, kscr_deTurckCoeff_component_eq (I := I) (M := M) g₀ ga x e horth K J,
      kscr_deTurckCoeff_component_eq (I := I) (M := M) g₀ gb x e horth K J, hΛ,
      ContinuousLinearMap.sub_apply, map_sub]
    ring
  rw [Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun J _ => hcompsq K J))]
  rw [kscr_deTurckCoeff_componentSqSum_eq n (fun a b => g₀.inner x (e a) (Λ (e b)))]
  have h1δa : (0 : ℝ) < 1 - δa := by linarith
  have h1δb : (0 : ℝ) < 1 - δb := by linarith
  have hr_nn : (0 : ℝ) ≤ δab / ((1 - δa) * (1 - δb)) :=
    div_nonneg hδab_nn (le_of_lt (mul_pos h1δa h1δb))
  set r : ℝ := δab / ((1 - δa) * (1 - δb)) with hr
  have hper : ∀ b : Fin n, g₀.inner x (Λ (e b)) (Λ (e b)) ≤ r ^ 2 := by
    intro b
    have hsqrt := DifferentialGeometry.Analysis.Sobolev.TensorHilbert.sqrt_inner_gInvDiffRaisedEndo_sub_le
      (I := I) (M := M) g₀ ga gb ha hb htie_a htie_b hδa_lt hδa hδb_lt hδb_nn hδb
      hδab_nn hδab x (e b)
    have hΛb : Λ (e b) = metricComparisonDiffEndo (I := I) g₀ ga x (e b)
        - metricComparisonDiffEndo (I := I) g₀ gb x (e b) := by
      rw [hΛ, ContinuousLinearMap.sub_apply]
    rw [← hΛb, ← hr] at hsqrt
    have he1 : g₀.inner x (e b) (e b) = 1 := by rw [horth b b]; simp
    rw [he1, Real.sqrt_one, mul_one] at hsqrt
    have hLnn : 0 ≤ g₀.inner x (Λ (e b)) (Λ (e b)) :=
      DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg (I := I) (M := M)
        g₀ x (Λ (e b))
    have hsq := Real.sq_sqrt hLnn
    nlinarith [Real.sqrt_nonneg (g₀.inner x (Λ (e b)) (Λ (e b))), hsqrt, hsq, hr_nn]
  have hParseval : ∀ b : Fin n,
      (∑ a : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2) = g₀.inner x (Λ (e b)) (Λ (e b)) := by
    intro b
    have hpb := hpar (Λ (e b))
    refine hpb ▸ ?_
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [g₀.symm x (e a) (Λ (e b))]
  have hAB : (∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2)
      ≤ (n : ℝ) * r ^ 2 := by
    rw [Finset.sum_comm]
    calc (∑ b : Fin n, ∑ a : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2)
        = ∑ b : Fin n, g₀.inner x (Λ (e b)) (Λ (e b)) :=
          Finset.sum_congr rfl (fun b _ => hParseval b)
      _ ≤ ∑ _b : Fin n, r ^ 2 := Finset.sum_le_sum (fun b _ => hper b)
      _ = (n : ℝ) * r ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  calc (n : ℝ) ^ 2 * ∑ a : Fin n, ∑ b : Fin n, (g₀.inner x (e a) (Λ (e b))) ^ 2
      ≤ (n : ℝ) ^ 2 * ((n : ℝ) * r ^ 2) := mul_le_mul_of_nonneg_left hAB hn_nn
    _ = (Module.finrank ℝ E : ℝ) ^ 3 * r ^ 2 := by rw [← hnE]; ring

omit [NeZero (Module.finrank ℝ E)] in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private lemma kscr_combinedTrace42Model_apply_symbolic
    (L : Tensor0SBundle.Tensor0SModel 1 ℝ E →L[ℝ] E)
    (D : Tensor0SBundle.Tensor0SModel 4 ℝ E) (m : Fin 2 → E) :
    ricciPrincipalCoeffDoubleTraceModel (E := E) L D m =
      (1 / 2 : ℝ) *
        (modelDoubleTrace (E := E) 2 L
            (ContinuousMultilinearMap.domDomCongr koszulDoubleTraceSlotPerm D) m
          + modelDoubleTrace (E := E) 2 L (ContinuousMultilinearMap.domDomCongr koszulDoubleTraceSlotPerm D)
              (fun j : Fin 2 => m ((Equiv.swap (0 : Fin 2) 1) j))
          - modelDoubleTrace (E := E) 2 L D m) := by
  rw [ricciPrincipalCoeffDoubleTraceModel, ContinuousLinearMap.smul_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma kscr_ricciArmPrincipalCoeff_sub_add_self_eq_reindexSum
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
        + (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₁
          - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀) =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
          (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁) koszulDoubleTraceSlotPerm
        + reindexCoeffGen (I := I) (M := M) g₀ 4 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 4 2 (Equiv.swap (0 : Fin 2) 1)
              (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁)) koszulDoubleTraceSlotPerm
        - deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  refine tensorRSSpace_ext 4 2 x (fun w => ?_)
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply,
    ricciArmPrincipalCoeff_toSection, ricciArmPrincipalCoeff_toSection,
    ricciArmPrincipalCoeffFib_toModel, ricciArmPrincipalCoeffFib_toModel,
    kscr_combinedTrace42Model_apply_symbolic, kscr_combinedTrace42Model_apply_symbolic]
  rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add, ContMDiffSection.coe_sub,
    ContMDiffSection.coe_add, Pi.sub_apply, Pi.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_add,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.add_apply]
  simp only [reindexCoeffGen_toSection, reindexCoeffFibGen_apply, rsDomDomCongrSection_toSection,
    toModel_rsDomDomCongr_apply, deTurckPrincipalCometricCoeff_toSection_clm_eq,
    cometricDoubleTraceFib_toModel,
    Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_sub, ContinuousLinearMap.sub_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.sub_apply]
  ring

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma kscr_traceHessianCoeff_sub_eq_reindex_pcc
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    traceHessianCoeff (I := I) (M := M) g₀ g₁ - traceHessianCoeff (I := I) (M := M) g₀ g₀ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁) traceHessianSlotPerm := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    traceHessianCoeff_toSection, traceHessianCoeff_toSection, reindexCoeffGen_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply,
    deTurckPrincipalCometricCoeff_toSection_clm_eq, ContinuousLinearMap.sub_apply,
    traceHessianFib, traceHessianFib, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, domDomCongrFib_apply]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem reindexCoeffGen_map_sub (g₀ : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g₀ 4 2) (ρ : Equiv.Perm (Fin 4)) :
    reindexCoeffGen (I := I) (M := M) g₀ 4 2 (A - B) ρ =
      reindexCoeffGen (I := I) (M := M) g₀ 4 2 A ρ -
        reindexCoeffGen (I := I) (M := M) g₀ 4 2 B ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    reindexCoeffGen_toSection, reindexCoeffGen_toSection, reindexCoeffGen_toSection,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply, reindexCoeffFibGen_apply,
    reindexCoeffFibGen_apply, ContinuousLinearMap.sub_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private theorem kscr_jointTotalSpaceRS_sub {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_sub (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
      (A p₀) (B p₀)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private theorem kscr_jointTotalSpaceRS_add {r s : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SBundle.TensorRSSpace r s I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p)) ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (B p)) ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel r s ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel r s ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z) p.1 (A p + B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := Tensor0SBundle.tensorRSBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) r s
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SBundle.TensorRSModel r s ℝ E)
    (fun z : M => Tensor0SBundle.TensorRSSpace r s I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace (F := Tensor0SBundle.TensorRSModel r s ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace r s I z)).mp (hB p₀ hp₀)
  refine (hA'.2.add hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀ ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by rw [he]; exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hx
    exact (e.linear ℝ hx).map_add (A p) (B p)
  · exact (e.linear ℝ (by rw [he, ← hx₀]; exact mem_baseSet_trivializationAt _ _ x₀)).map_add
      (A p₀) (B p₀)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
omit [BoundarylessManifold I M] in
private lemma kscr_phiMet_realizedFam_eq_lieSubLich
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (s : ℝ) :
    deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg (realizedFam (I := I) g₀ T T' hδ hδ' s) =
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff
          (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg
        - (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s
            + linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' s) := by
  rw [deTurckPhiMetTotal, linearizedRicciArm2FieldLichnerowicz]
  set X : SmoothCcTensor g₀ 4 2 :=
    ricciArmPrincipalCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hX
  set Y : SmoothCcTensor g₀ 4 2 :=
    traceHessianCoeff (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) with hY
  have hhalf : (1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y = Y := by
    rw [← add_smul]
    norm_num
  have hgrp : (X - (1 / 2 : ℝ) • Y) + (X - (1 / 2 : ℝ) • Y) =
      (X + X) - ((1 / 2 : ℝ) • Y + (1 / 2 : ℝ) • Y) := by abel
  rw [hgrp, hhalf]
  abel

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
theorem deTurckPhiMetTotal_jointSmooth_along_realizedFam
    (g₀ g_bg : SmoothRiemannianMetric I M) (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4
      (fun s => deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T T' hδ hδ' s)) (δ := δ) (δ' := δ') := by
  have hLie :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff_realizedFam_jointSmooth
      (I := I) g₀ T T' hδ hδ' g_bg
  have hLich := linearizedRicci_arm2FieldLichnerowicz_jointSmooth (I := I) g₀ T T' hδ hδ'
  have hadd := kscr_jointTotalSpaceRS_add (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    hLich hLich
  have hsub := kscr_jointTotalSpaceRS_sub (I := I) (r := 4) (s := 2)
    (S := realizedSmallSet (δ := δ) (δ' := δ'))
    (fun p : M × ℝ =>
      (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.deTurckLieArm2PrincipalCoeff
        (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' p.2) g_bg).toSection p.1)
    (fun p : M × ℝ =>
      (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1
        + (linearizedRicciArm2FieldLichnerowicz (I := I) g₀ T T' hδ hδ' p.2).toSection p.1)
    hLie hadd
  refine hsub.congr (fun p _ => ?_)
  beta_reduce
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
    (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1 t) ?_
  rw [kscr_phiMet_realizedFam_eq_lieSubLich (I := I) (M := M) g₀ g_bg T T' hδ hδ' p.2,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]

set_option maxHeartbeats 25600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
theorem exists_deTurckPhiTotPathIntegral_sub_background_sub_principalCometricCoeff_fibreSup_le
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (_ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    {δ : ℝ} (hδ_le : δ ≤ 1 / 3)
    (hδ_fibre : ∀ (T₀ : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
      metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T₀) δ) :
    ∃ εCD : ℝ, 0 ≤ εCD ∧
      (0 ≤ δ → εCD ≤ 3 * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ∧
      ∀ (T₀ : SmoothCcTensor g₀ 0 2),
        (∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T₀ x v w = smoothCcTensorBilinForm (I := I) g₀ T₀ x w v) →
        ∀ (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀),
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
            ((deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
                  (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                  (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
                    (by
                      rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
                          from (zero_smul _ _).symm, smoothCcToTensorHs_smul,
                        tensorHs_norm_smul]
                      simpa using hR₀)) -
                deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀ -
                deTurckPrincipalCometricCoeff (I := I) (M := M) g₀
                  (tensorSectionRealizeMetric (I := I) g₀ T₀
                    (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
                    (hδ_fibre T₀ hball))).toSection x) ≤ εCD ^ 2 := by
  classical
  have hfC_nn : (0 : ℝ) ≤ deTurckArmFibreConst (Module.finrank ℝ E) :=
    deTurckArmFibreConst_nonneg _
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have h1δ : (0 : ℝ) < 1 - δ := by linarith
  rcases isEmpty_or_nonempty M with hM | hM
  · refine ⟨0, le_refl 0, fun hδ0' => ?_, fun T₀ hTsymm hball x => (hM.false x).elim⟩
    have hκ_nn : (0 : ℝ) ≤ δ / (1 - δ) := div_nonneg hδ0' (le_of_lt h1δ)
    positivity
  · have hδ0 : 0 ≤ δ :=
      delta_nonneg_of_ball_gFibreOpBound (I := I) (M := M) g₀ a hR₀ hδ_fibre
    have hκ_nn : (0 : ℝ) ≤ δ / (1 - δ) := div_nonneg hδ0 (le_of_lt h1δ)
    refine ⟨(11 / 4 : ℝ) * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ)),
      mul_nonneg (mul_nonneg (by norm_num) hfC_nn) hκ_nn,
      fun _ => by nlinarith [mul_nonneg hfC_nn hκ_nn], ?_⟩
    intro T₀ hTsymm hball x
    set fC : ℝ := deTurckArmFibreConst (Module.finrank ℝ E) with hfC_def
    have hfC_sqrt : fC = Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) := rfl
    set κ : ℝ := δ / (1 - δ) with hκ_def
    have hδT := hδ_fibre T₀ hball
    have hδZ := hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
      (by
        rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
            from (zero_smul _ _).symm, smoothCcToTensorHs_smul, tensorHs_norm_smul]
        simpa using hR₀)
    set g₁ : SmoothRiemannianMetric I M := tensorSectionRealizeMetric (I := I) g₀ T₀
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) with hg₁_def
    set P : SmoothCcTensor g₀ 4 2 := deTurckPhiTotPathIntegral (I := I) (M := M) g₀ g_bg T₀
      (0 : SmoothCcTensor g₀ 0 2)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball)
      (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1))
      (hδ_fibre (0 : SmoothCcTensor g₀ 0 2)
        (by
          rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g₀ 0 2)
              from (zero_smul _ _).symm, smoothCcToTensorHs_smul, tensorHs_norm_smul]
          simpa using hR₀)) with hP_def
    set C1 : SmoothCcTensor g₀ 4 2 := deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g₀
      with hC1_def
    set Δ1 : SmoothCcTensor g₀ 4 2 := deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g₁
      with hΔ1_def
    set Φ : ℝ → SmoothCcTensor g₀ 4 2 := fun s =>
      deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
        (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ s) with hΦ_def
    have hjoint : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ 4 Φ
        (δ := δ) (δ' := δ) :=
      deTurckPhiMetTotal_jointSmooth_along_realizedFam (I := I) (M := M) g₀ g_bg T₀
        (0 : SmoothCcTensor g₀ 0 2) hδT hδZ
    have hSIu : Set.uIcc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) := by
      rw [Set.uIcc_of_le zero_le_one]
      exact Icc_subset_realizedSmallSet hδ_lt hδ_lt
    have hIccS : Set.Icc (0 : ℝ) 1 ⊆ realizedSmallSet (δ := δ) (δ' := δ) :=
      Icc_subset_realizedSmallSet hδ_lt hδ_lt
    have hjointC : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel 4 2 ℝ E)) ∞
        (fun p : M × ℝ => TotalSpace.mk' (Tensor0SBundle.TensorRSModel 4 2 ℝ E)
          (E := fun z : M => Tensor0SBundle.TensorRSSpace 4 2 I z) p.1
          ((Φ p.2).toSection p.1))
        ((Set.univ : Set M) ×ˢ realizedSmallSet (δ := δ) (δ' := δ)) := by
      have h := hjoint
      rw [linearizedRicciThreeArmHjoint] at h
      exact h
    have hslice : ContinuousOn (fun t : ℝ =>
        Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x))
        (realizedSmallSet (δ := δ) (δ' := δ)) :=
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.jointContMDiff_toModel_continuous_slice
        (I := I) g₀ 4 2 Φ (realizedSmallSet (δ := δ) (δ' := δ)) hjointC x
    have hcontIcc : ContinuousOn (fun t : ℝ =>
        Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x)) (Set.Icc (0 : ℝ) 1) :=
      hslice.mono hIccS
    set Cx : Tensor0SBundle.TensorRSModel 4 2 ℝ E :=
      Tensor0SBundle.TensorRSSpace.toModel (C1.toSection x)
        + Tensor0SBundle.TensorRSSpace.toModel (Δ1.toSection x) with hCx_def
    have hsecPD : ((P - C1 - Δ1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
        P.toSection x - C1.toSection x - Δ1.toSection x := by
      rw [show ((P - C1 - Δ1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
          (P - C1).toSection x - Δ1.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [show ((P - C1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
          P.toSection x - C1.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
    have hint_fPhi : IntervalIntegrable (fun t : ℝ =>
        Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x))
        MeasureTheory.volume 0 1 :=
      (hslice.mono hSIu).intervalIntegrable
    have hDmodel : Tensor0SBundle.TensorRSSpace.toModel ((P - C1 - Δ1).toSection x) =
        ∫ t in (0 : ℝ)..1,
          (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx) := by
      rw [hsecPD, Tensor0SBundle.TensorRSSpace.toModel_sub,
        Tensor0SBundle.TensorRSSpace.toModel_sub]
      rw [show Tensor0SBundle.TensorRSSpace.toModel (P.toSection x) =
          ∫ t in (0 : ℝ)..1, Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) from by
        rw [hP_def]
        unfold deTurckPhiTotPathIntegral
        rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.pathIntegralCoeffField_toModel]]
      rw [intervalIntegral.integral_sub hint_fPhi intervalIntegrable_const,
        intervalIntegral.integral_const, hCx_def]
      norm_num
      abel
    clear_value P C1 Δ1 g₁ Φ Cx
    have htpn_val : ∀ (W : SmoothCcTensor g₀ 4 2),
        tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
            (Tensor0SBundle.TensorRSSpace.toModel (W.toSection x)) =
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (W.toSection x)) := by
      intro W
      rw [riemannianFiberNormSq_eq_tensorInnerPointwise]
      rfl
    have htpn_neg : ∀ m : Tensor0SBundle.TensorRSModel 4 2 ℝ E,
        tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x (-m) =
          tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x m := by
      intro m
      unfold tensorPointwiseNorm
      rw [show (-m : Tensor0SBundle.TensorRSModel 4 2 ℝ E) = (-1 : ℝ) • m from
        (neg_one_smul ℝ m).symm, tensorInnerPointwise_smul_left,
        tensorInnerPointwise_smul_right]
      norm_num
    have hsqrt_n3 : ∀ r : ℝ, 0 ≤ r →
        Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3 * r ^ 2) = fC * r := by
      intro r hr
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hr, hfC_sqrt]
    have hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
            (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx) ≤
          fC * κ * (4 * t + (3 / 2) * (1 - t)) := by
      intro t ht
      have ht0 : (0 : ℝ) ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      set g_t : SmoothRiemannianMetric I M :=
        realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t with hg_t_def
      set Δt : SmoothCcTensor g₀ 4 2 :=
        deTurckPrincipalCometricCoeff (I := I) (M := M) g₀ g_t with hΔt_def
      clear_value Δt
      have htδ_nn : (0 : ℝ) ≤ t * δ := mul_nonneg ht0 hδ0
      have htδ_le : t * δ ≤ δ := by nlinarith
      have htδ_lt : t * δ < 1 := lt_of_le_of_lt htδ_le hδ_lt
      have h1tδ : (0 : ℝ) < 1 - t * δ := by linarith
      have htie_t : ∀ (y : M) (v w : TangentSpace I y),
          g_t.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀
              (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t) y v w :=
        fun y v w => realizedFam_inner_of_mem (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2)
          hδT hδZ (hIccS ht) y v w
      clear_value g_t
      have hcp : convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t
          = t • T₀ := by
        rw [show convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t =
            (1 - t) • (0 : SmoothCcTensor g₀ 0 2) + t • T₀ from rfl, smul_zero, zero_add]
      have hbilin_cp : ∀ (y : M) (v w : TangentSpace I y),
          ccTensorBilinSymm (I := I) g₀
            (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t) y v w =
            t * ccTensorBilinSymm (I := I) g₀ T₀ y v w := by
        intro y v w
        rw [hcp, ccTensorBilinSymm_smul]
      have hδa : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t)) (t * δ) := by
        intro y v w
        rw [hbilin_cp y v w, abs_mul, abs_of_nonneg ht0]
        have hbase := hδT y v w
        have hs1 : (0 : ℝ) ≤ Real.sqrt (g₀.inner y v v) := Real.sqrt_nonneg _
        have hs2 : (0 : ℝ) ≤ Real.sqrt (g₀.inner y w w) := Real.sqrt_nonneg _
        calc t * |ccTensorBilinSymm (I := I) g₀ T₀ y v w|
            ≤ t * (δ * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w)) :=
              mul_le_mul_of_nonneg_left hbase ht0
          _ = t * δ * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) := by ring
      have hδab : metricCauchySchwarzBound (I := I) (M := M) g₀
          (fun y => ccTensorBilinSymm (I := I) g₀
              (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t) y
            - ccTensorBilinSymm (I := I) g₀ T₀ y) ((1 - t) * δ) := by
        intro y v w
        beta_reduce
        have hval : (ccTensorBilinSymm (I := I) g₀
            (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t) y
            - ccTensorBilinSymm (I := I) g₀ T₀ y) v w =
            ccTensorBilinSymm (I := I) g₀
              (convexPerturbation (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) t) y v w
              - ccTensorBilinSymm (I := I) g₀ T₀ y v w := rfl
        rw [hval, hbilin_cp y v w]
        have hfact : t * (ccTensorBilinSymm (I := I) g₀ T₀ y v w)
            - ccTensorBilinSymm (I := I) g₀ T₀ y v w =
            (t - 1) * (ccTensorBilinSymm (I := I) g₀ T₀ y v w) := by ring
        rw [hfact, abs_mul, abs_of_nonpos (by linarith : t - 1 ≤ 0)]
        have hbase := hδT y v w
        have habs_nn : (0 : ℝ) ≤ |ccTensorBilinSymm (I := I) g₀ T₀ y v w| := abs_nonneg _
        calc -(t - 1) * |ccTensorBilinSymm (I := I) g₀ T₀ y v w|
            = (1 - t) * |ccTensorBilinSymm (I := I) g₀ T₀ y v w| := by ring
          _ ≤ (1 - t) * (δ * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w)) :=
              mul_le_mul_of_nonneg_left hbase (by linarith)
          _ = (1 - t) * δ * Real.sqrt (g₀.inner y v v) * Real.sqrt (g₀.inner y w w) := by ring
      have htie_1 : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T₀ y v w := by
        intro y v w
        rw [hg₁_def]
        exact tensorSectionRealizeMetric_inner (I := I) g₀ T₀
          (lt_of_le_of_lt hδ_le (by norm_num : (1 : ℝ) / 3 < 1)) (hδ_fibre T₀ hball) y v w
      have hΔt_rfns : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) ≤
          (Module.finrank ℝ E : ℝ) ^ 3 * (t * δ / (1 - t * δ)) ^ 2 := by
        rw [hΔt_def]
        exact riemannianFiberNormSq_deTurckPrincipalCometricCoeff_le (I := I) (M := M)
          g₀ g_t _ htie_t htδ_lt htδ_nn hδa x
      have hΔt_sqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          (Δt.toSection x)) ≤ fC * (t * δ / (1 - t * δ)) := by
        refine le_trans (Real.sqrt_le_sqrt hΔt_rfns) ?_
        rw [hsqrt_n3 _ (div_nonneg htδ_nn (le_of_lt h1tδ))]
      have hdev_rfns : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((Δt - Δ1).toSection x) ≤
          (Module.finrank ℝ E : ℝ) ^ 3 *
            ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) ^ 2 := by
        rw [hΔt_def, hΔ1_def]
        exact riemannianFiberNormSq_deTurckPrincipalCometricCoeff_sub_le (I := I) (M := M) g₀ g_t g₁ _ _
          htie_t htie_1 htδ_lt hδa hδ_lt hδ0 hδT
          (mul_nonneg (by linarith) hδ0) hδab htδ_nn x
      have hdev_sqrt : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x
          ((Δt - Δ1).toSection x)) ≤
          fC * ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) := by
        refine le_trans (Real.sqrt_le_sqrt hdev_rfns) ?_
        rw [hsqrt_n3 _ (div_nonneg (mul_nonneg (by linarith) hδ0)
          (le_of_lt (mul_pos h1tδ h1δ)))]
      have hdec_t := deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g_t
      have hdec_0 := deTurckPhiMetTotal_eq_reindex_decomp_fw (I := I) (M := M) g₀ g_bg g₀
      set ρA : Equiv.Perm (Fin 4) := traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermA
        with hρA_def
      set ρAT : Equiv.Perm (Fin 4) := traceHessianSlotPerm⁻¹ * deTurckLieArm2DivSlotPermAT
        with hρAT_def
      set A1 : SmoothCcTensor g₀ 4 2 := reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 Δt traceHessianSlotPerm) ρA with hA1_def
      set A2 : SmoothCcTensor g₀ 4 2 := reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 Δt traceHessianSlotPerm) ρAT with hA2_def
      set R1 : SmoothCcTensor g₀ 4 2 := reindexCoeffGen (I := I) (M := M) g₀ 4 2 Δt
        koszulDoubleTraceSlotPerm with hR1_def
      set R2 : SmoothCcTensor g₀ 4 2 := reindexCoeffGen (I := I) (M := M) g₀ 4 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 4 2 (Equiv.swap (0 : Fin 2) 1) Δt)
        koszulDoubleTraceSlotPerm with hR2_def
      clear_value A1 A2 R1 R2
      have hXX : (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t
            + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t)
          - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀
            + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀) = R1 + R2 - Δt := by
        have h691 := kscr_ricciArmPrincipalCoeff_sub_add_self_eq_reindexSum
          (I := I) (M := M) g₀ g_t
        calc (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t
              + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t)
            - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀
              + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
            = (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀)
              + (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t
                - ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀) := by abel
          _ = R1 + R2 - Δt := by rw [h691, hR1_def, hR2_def, hΔt_def]
      have hΨ : Φ t - C1 - Δ1 = A1 + A2 - R1 - R2 + (Δt - Δ1) := by
        have h327 := kscr_traceHessianCoeff_sub_eq_reindex_pcc (I := I) (M := M) g₀ g_t
        calc Φ t - C1 - Δ1
            = (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                  (traceHessianCoeff (I := I) (M := M) g₀ g_t) ρA
                - reindexCoeffGen (I := I) (M := M) g₀ 4 2
                  (traceHessianCoeff (I := I) (M := M) g₀ g₀) ρA)
              + (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                  (traceHessianCoeff (I := I) (M := M) g₀ g_t) ρAT
                - reindexCoeffGen (I := I) (M := M) g₀ 4 2
                  (traceHessianCoeff (I := I) (M := M) g₀ g₀) ρAT)
              - ((ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t
                  + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g_t)
                - (ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀
                  + ricciArmPrincipalCoeff (I := I) (M := M) g₀ g₀))
              - Δ1 := by
              rw [hΦ_def]
              beta_reduce
              rw [show deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg
                  (realizedFam (I := I) g₀ T₀ (0 : SmoothCcTensor g₀ 0 2) hδT hδZ t) =
                  deTurckPhiMetTotal (I := I) (M := M) g₀ g_bg g_t from by rw [hg_t_def]]
              rw [hdec_t, hC1_def, hdec_0, hρA_def, hρAT_def]
              abel
          _ = (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g_t
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀) ρA)
              + (reindexCoeffGen (I := I) (M := M) g₀ 4 2
                (traceHessianCoeff (I := I) (M := M) g₀ g_t
                  - traceHessianCoeff (I := I) (M := M) g₀ g₀) ρAT)
              - (R1 + R2 - Δt) - Δ1 := by
              rw [reindexCoeffGen_map_sub (I := I) (M := M) g₀ _ _ ρA,
                reindexCoeffGen_map_sub (I := I) (M := M) g₀ _ _ ρAT, hXX]
          _ = A1 + A2 - R1 - R2 + (Δt - Δ1) := by
              rw [h327, ← hΔt_def, hA1_def, hA2_def]
              abel
      have hΨsec : ((Φ t - C1 - Δ1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
          A1.toSection x + A2.toSection x - R1.toSection x - R2.toSection x
            + (Δt - Δ1).toSection x := by
        rw [hΨ]
        rw [show ((A1 + A2 - R1 - R2 + (Δt - Δ1)).toSection x :
            Tensor0SBundle.TensorRSSpace 4 2 I x) =
            (A1 + A2 - R1 - R2).toSection x + (Δt - Δ1).toSection x from by
          rw [SmoothCcTensor.toSection_add]; rfl]
        rw [show ((A1 + A2 - R1 - R2).toSection x :
            Tensor0SBundle.TensorRSSpace 4 2 I x) =
            (A1 + A2 - R1).toSection x - R2.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [show ((A1 + A2 - R1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
            (A1 + A2).toSection x - R1.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [show ((A1 + A2).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
            A1.toSection x + A2.toSection x from by
          rw [SmoothCcTensor.toSection_add]; rfl]
      have hΨmodel : Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx =
          Tensor0SBundle.TensorRSSpace.toModel ((Φ t - C1 - Δ1).toSection x) := by
        rw [show ((Φ t - C1 - Δ1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
            (Φ t - C1).toSection x - Δ1.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [show ((Φ t - C1).toSection x : Tensor0SBundle.TensorRSSpace 4 2 I x) =
            (Φ t).toSection x - C1.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [Tensor0SBundle.TensorRSSpace.toModel_sub,
          Tensor0SBundle.TensorRSSpace.toModel_sub, hCx_def]
        abel
      have hexA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (A1.toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) := by
        rw [hA1_def]
        rw [reindexCoeffGen_toSection]
        rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
          (I := I) (M := M) g₀ 4 2 x ρA _]
        rw [reindexCoeffGen_toSection]
        exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
          (I := I) (M := M) g₀ 4 2 x traceHessianSlotPerm _
      have hexA2 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (A2.toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) := by
        rw [hA2_def]
        rw [reindexCoeffGen_toSection]
        rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
          (I := I) (M := M) g₀ 4 2 x ρAT _]
        rw [reindexCoeffGen_toSection]
        exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
          (I := I) (M := M) g₀ 4 2 x traceHessianSlotPerm _
      have hexR1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R1.toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) := by
        rw [hR1_def, reindexCoeffGen_toSection]
        exact DifferentialGeometry.Analysis.Parabolic.TensorSpectral.riemannianFiberNormSq_reindexCoeffFibGen
          (I := I) (M := M) g₀ 4 2 x koszulDoubleTraceSlotPerm _
      have hexR2 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (R2.toSection x) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) := by
        have h20 := rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 4 2
          koszulDoubleTraceSlotPerm (Equiv.swap (0 : Fin 2) 1) Δt 0 x
        rw [hR2_def]
        simpa [iteratedCovGrad_zero] using h20
      have htpn_piece : ∀ (W : SmoothCcTensor g₀ 4 2),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (W.toSection x) =
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (Δt.toSection x) →
          tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
              (Tensor0SBundle.TensorRSSpace.toModel (W.toSection x)) ≤
            fC * (t * δ / (1 - t * δ)) := by
        intro W hW
        rw [htpn_val W, hW]
        exact hΔt_sqrt
      have htpn_sub_le : ∀ u v : Tensor0SBundle.TensorRSModel 4 2 ℝ E,
          tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x (u - v) ≤
            tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x u
              + tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x v := by
        intro u v
        rw [sub_eq_add_neg]
        refine le_trans (tensorPointwiseNorm_add_le (I := I) (M := M) g₀ 4 2 x u (-v)) ?_
        rw [htpn_neg v]
      have htri : tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
          (Tensor0SBundle.TensorRSSpace.toModel ((Φ t - C1 - Δ1).toSection x)) ≤
          4 * (fC * (t * δ / (1 - t * δ)))
            + fC * ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) := by
        rw [hΨsec]
        rw [Tensor0SBundle.TensorRSSpace.toModel_add, Tensor0SBundle.TensorRSSpace.toModel_sub,
          Tensor0SBundle.TensorRSSpace.toModel_sub, Tensor0SBundle.TensorRSSpace.toModel_add]
        have t4 := tensorPointwiseNorm_add_le (I := I) (M := M) g₀ 4 2 x
          (Tensor0SBundle.TensorRSSpace.toModel (A1.toSection x)
            + Tensor0SBundle.TensorRSSpace.toModel (A2.toSection x)
            - Tensor0SBundle.TensorRSSpace.toModel (R1.toSection x)
            - Tensor0SBundle.TensorRSSpace.toModel (R2.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel ((Δt - Δ1).toSection x))
        have t3 := htpn_sub_le
          (Tensor0SBundle.TensorRSSpace.toModel (A1.toSection x)
            + Tensor0SBundle.TensorRSSpace.toModel (A2.toSection x)
            - Tensor0SBundle.TensorRSSpace.toModel (R1.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (R2.toSection x))
        have t2 := htpn_sub_le
          (Tensor0SBundle.TensorRSSpace.toModel (A1.toSection x)
            + Tensor0SBundle.TensorRSSpace.toModel (A2.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (R1.toSection x))
        have t1 := tensorPointwiseNorm_add_le (I := I) (M := M) g₀ 4 2 x
          (Tensor0SBundle.TensorRSSpace.toModel (A1.toSection x))
          (Tensor0SBundle.TensorRSSpace.toModel (A2.toSection x))
        have b1 := htpn_piece A1 hexA1
        have b2 := htpn_piece A2 hexA2
        have b3 := htpn_piece R1 hexR1
        have b4 := htpn_piece R2 hexR2
        have b5 : tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
            (Tensor0SBundle.TensorRSSpace.toModel ((Δt - Δ1).toSection x)) ≤
            fC * ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) := by
          rw [htpn_val (Δt - Δ1)]
          exact hdev_sqrt
        linarith [t1, t2, t3, t4, b1, b2, b3, b4, b5]
      have hrate1 : t * δ / (1 - t * δ) ≤ t * κ := by
        rw [hκ_def, div_le_iff₀ h1tδ]
        have h1 : t * (δ / (1 - δ)) * (1 - t * δ) = (t * δ * (1 - t * δ)) / (1 - δ) := by
          field_simp
        rw [h1, le_div_iff₀ h1δ]
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ht0 hδ0) hδ0)
          (by linarith : (0:ℝ) ≤ 1 - t)]
      have hrate2 : (1 - t) * δ / ((1 - t * δ) * (1 - δ)) ≤ (3 / 2) * ((1 - t) * κ) := by
        rw [hκ_def, div_le_iff₀ (mul_pos h1tδ h1δ)]
        have h1 : (3 / 2 : ℝ) * ((1 - t) * (δ / (1 - δ))) * ((1 - t * δ) * (1 - δ)) =
            (3 / 2) * ((1 - t) * δ) * (1 - t * δ) := by
          field_simp
        rw [h1]
        have hkey : (0 : ℝ) ≤ 1 / 2 - (3 / 2) * (t * δ) := by nlinarith
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) hδ0) hkey]
      calc tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
            (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)
          = tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
            (Tensor0SBundle.TensorRSSpace.toModel ((Φ t - C1 - Δ1).toSection x)) := by
            rw [hΨmodel]
        _ ≤ 4 * (fC * (t * δ / (1 - t * δ)))
            + fC * ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) := htri
        _ ≤ 4 * (fC * (t * κ)) + fC * ((3 / 2) * ((1 - t) * κ)) := by
            have e1 : fC * (t * δ / (1 - t * δ)) ≤ fC * (t * κ) :=
              mul_le_mul_of_nonneg_left hrate1 hfC_nn
            have e2 : fC * ((1 - t) * δ / ((1 - t * δ) * (1 - δ))) ≤
                fC * ((3 / 2) * ((1 - t) * κ)) :=
              mul_le_mul_of_nonneg_left hrate2 hfC_nn
            linarith
        _ = fC * κ * (4 * t + (3 / 2) * (1 - t)) := by ring
    have hrfns_tpn : riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
        ((P - C1 - Δ1).toSection x) =
        tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
          (Tensor0SBundle.TensorRSSpace.toModel ((P - C1 - Δ1).toSection x)) ^ 2 := by
      rw [riemannianFiberNormSq_eq_tensorInnerPointwise]
      unfold tensorPointwiseNorm
      rw [Real.sq_sqrt (tensorInnerPointwise_nonneg (I := I) (M := M) g₀ 4 2 x _)]
    rw [hrfns_tpn, hDmodel]
    have hcont_shift : ContinuousOn (fun t : ℝ =>
        Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)
        (Set.Icc (0 : ℝ) 1) := hcontIcc.sub continuousOn_const
    have hint_le := tensorPointwiseNorm_intervalIntegral_le (I := I) (M := M) g₀ 4 2 x
      (fun t => Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx) hcont_shift
    have hint1 : IntervalIntegrable (fun t : ℝ =>
        tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
          (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx))
        MeasureTheory.volume 0 1 :=
      ((tensorPointwiseNorm_continuous (I := I) (M := M) g₀ 4 2 x).comp_continuousOn
        hcont_shift).intervalIntegrable_of_Icc (by norm_num)
    have hint2 : IntervalIntegrable (fun t : ℝ => fC * κ * (4 * t + (3 / 2) * (1 - t)))
        MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable
      continuity
    have hmono : (∫ t in (0 : ℝ)..1, tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
        (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)) ≤
        ∫ t in (0 : ℝ)..1, fC * κ * (4 * t + (3 / 2) * (1 - t)) :=
      intervalIntegral.integral_mono_on (by norm_num) hint1 hint2 hsup
    have hwval : (∫ t in (0 : ℝ)..1, fC * κ * (4 * t + (3 / 2) * (1 - t))) =
        (11 / 4) * fC * κ := by
      rw [intervalIntegral.integral_const_mul]
      rw [show (fun t : ℝ => 4 * t + (3 / 2) * (1 - t)) =
          fun t : ℝ => (5 / 2) * t + 3 / 2 from funext fun t => by ring]
      rw [intervalIntegral.integral_add ((intervalIntegral.intervalIntegrable_id).const_mul _)
        intervalIntegrable_const]
      rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
      norm_num
      ring
    have htpn_nn : (0 : ℝ) ≤ tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
        (∫ t in (0 : ℝ)..1,
          (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)) :=
      tensorPointwiseNorm_nonneg (I := I) (M := M) g₀ 4 2 x _
    have hfinal : tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
        (∫ t in (0 : ℝ)..1,
          (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)) ≤
        (11 / 4) * fC * κ := by
      refine le_trans hint_le ?_
      rw [← hwval]
      exact hmono
    calc tensorPointwiseNorm (I := I) (M := M) g₀ 4 2 x
          (∫ t in (0 : ℝ)..1,
            (Tensor0SBundle.TensorRSSpace.toModel ((Φ t).toSection x) - Cx)) ^ 2
        ≤ ((11 / 4) * fC * κ) ^ 2 := by
          exact pow_le_pow_left₀ htpn_nn hfinal 2
      _ = ((11 / 4 : ℝ) * deTurckArmFibreConst (Module.finrank ℝ E) * (δ / (1 - δ))) ^ 2 := by
          rw [hfC_def, hκ_def]

end

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
