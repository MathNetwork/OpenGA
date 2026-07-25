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
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBoundCoeffFieldOrderZeroBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBoundLoweredKernelTensors
import DifferentialGeometry.Tensor.Auxiliary.DeTurckLieKernelL2JetBoundGridWindow
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBoundCometricTraceFrame


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

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

section DLaGridBrick

open Tensor0SBundle
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [NeZero (Module.finrank ℝ E)] in
private theorem dLaLoweredCc_raise_repr (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
        (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) =
      dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hexp_sub : ∀ (F G : SmoothCcTensor g₀ 1 3),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from ((F - G).toSection x)) om) w =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from (F.toSection x)) om) w -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from (G.toSection x)) om) w := by
    intro F G
    rw [show ((F - G).toSection x) = F.toSection x - G.toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (F.toSection x - G.toSection x)) om) =
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from F.toSection x) om -
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from G.toSection x) om from rfl]
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  have hexp_add : ∀ (F G : SmoothCcTensor g₀ 1 3),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from ((F + G).toSection x)) om) w =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from (F.toSection x)) om) w +
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from (G.toSection x)) om) w := by
    intro F G
    rw [show ((F + G).toSection x) = F.toSection x + G.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (F.toSection x + G.toSection x)) om) =
        (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from F.toSection x) om +
          (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from G.toSection x) om from rfl]
    rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  have hA : ∀ (gc : SmoothRiemannianMetric I M),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) gc g₀)).toSection x) om)
        w =
      cotangentToDual (I := I) (x := x) om
        (covDerivConnDiff (I := I) g₀ gc
          (smoothExtensionTangent (I := I) x (w 0))
          (smoothExtensionTangent (I := I) x (w 2))
          (smoothExtensionTangent (I := I) x (w 1)) x) := by
    intro gc
    have hb := connDiffSection_covGrad_eq_covDerivConnDiff (I := I) gc g₀
      (dLaCovectorExtensionSection (I := I) (M := M) g₀ x om)
      (smoothExtensionTangentSection (I := I) (M := M) x (w 0))
      (smoothExtensionTangentSection (I := I) (M := M) x (w 1))
      (smoothExtensionTangentSection (I := I) (M := M) x (w 2)) x
    rw [dLaCovectorExtensionSection_self (I := I) (M := M) g₀ x om] at hb
    rw [show smoothExtensionTangentSection (I := I) (M := M) x (w 0) x = w 0 from
      smoothExtensionTangent_eq (I := I) x (w 0)] at hb
    rw [show smoothExtensionTangentSection (I := I) (M := M) x (w 1) x = w 1 from
      smoothExtensionTangent_eq (I := I) x (w 1)] at hb
    rw [show smoothExtensionTangentSection (I := I) (M := M) x (w 2) x = w 2 from
      smoothExtensionTangent_eq (I := I) x (w 2)] at hb
    rw [show (Fin.cons (w 0) (Fin.cons (w 1) ![w 2]) : Fin 3 → TangentSpace I x) = w from by
      funext k
      refine Fin.cases rfl (fun j => ?_) k
      refine Fin.cases rfl (fun j' => ?_) j
      refine Fin.cases rfl (fun j'' => j''.elim0) j'] at hb
    rw [hb]
    rw [show covDerivConnDiff (I := I) g₀ gc
        (fun b => smoothExtensionTangentSection (I := I) (M := M) x (w 0) b)
        (fun b => smoothExtensionTangentSection (I := I) (M := M) x (w 2) b)
        (fun b => smoothExtensionTangentSection (I := I) (M := M) x (w 1) b) x =
      covDerivConnDiff (I := I) g₀ gc
        (smoothExtensionTangent (I := I) x (w 0))
        (smoothExtensionTangent (I := I) x (w 2))
        (smoothExtensionTangent (I := I) x (w 1)) x from rfl]
    exact (cotangentToDual_apply (I := I) (x := x) om _).symm
  have hswap0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := Equiv.swap_apply_left 0 2
  have hswap1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
  have hswap2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := Equiv.swap_apply_right 0 2
  have hrot0 : (finRotate 3) (0 : Fin 3) = 1 := by decide
  have hrot1 : (finRotate 3) (1 : Fin 3) = 2 := by decide
  have hrot2 : (finRotate 3) (2 : Fin 3) = 0 := by decide
  have hQperm : ∀ (σ : Equiv.Perm (Fin 3)) (ga gb : SmoothRiemannianMetric I M),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ
            (dLaQuadCc (I := I) (M := M) g₀ ga gb)).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) gb g₀ x
          (PDE.DeTurck.connDiff (I := I) ga g₀ x (w (σ 1)) (w (σ 2))) (w (σ 0))) := by
    intro σ ga gb
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ
          (dLaQuadCc (I := I) (M := M) g₀ ga gb)).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          tensorRS_domDomCongr σ ((dLaQuadCc (I := I) (M := M) g₀ ga gb).toSection x)) om) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) σ
      ((dLaQuadCc (I := I) (M := M) g₀ ga gb).toSection x) om]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact dLaQuadCc_toModel (I := I) (M := M) g₀ ga gb x om (fun i => w (σ i))
  have hL : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
          (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (connDiffCovDerivOp (I := I) g₁ g_bg x (w 0) (w 1) (w 2)) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
          (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          cometricRaiseSlot0Fib g₀ 2 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
              (unitTensor (I := I) (M := M) x))) om) from by
      rw [cometricRaiseSlot0Field_toSection]]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 2 x _ om]
    rw [interiorProduct_toModel_eval_dla (I := I) (M := M) 3 x
      (inverseMetricSharpFib (I := I) g₀ x om) _ w]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
          (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
          (unitTensor (I := I) (M := M) x)) =
        unitModel (I := I) (M := M) g₀ 4 (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x
        from rfl]
    rw [dLaLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x]
    rw [show (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 4 → TangentSpace I x) 0 =
        inverseMetricSharpFib (I := I) g₀ x om from rfl]
    rw [show (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 4 → TangentSpace I x) 1 = w 0 from rfl]
    rw [show (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 4 → TangentSpace I x) 2 = w 1 from rfl]
    rw [show (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 4 → TangentSpace I x) 3 = w 2 from rfl]
    rw [cotangentToDual_eq_inner_sharp_dla (I := I) (M := M) g₀ x om
      (connDiffCovDerivOp (I := I) g₁ g_bg x (w 0) (w 1) (w 2))]
  rw [hL]
  rw [dLaKernelRaisedCc]
  rw [hexp_add, hexp_sub, hexp_add, hexp_sub, hexp_sub, hexp_add, hexp_sub]
  rw [hA g₁, hA g_bg]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g₁).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 2)) (w 0)) from
    dLaQuadCc_toModel (I := I) (M := M) g₀ g₁ g₁ x om w]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (dLaQuadCc (I := I) (M := M) g₀ g_bg g₁).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x (w 1) (w 2)) (w 0)) from
    dLaQuadCc_toModel (I := I) (M := M) g₀ g_bg g₁ x om w]
  rw [hQperm (Equiv.swap (0 : Fin 3) 2) g₁ g₁, hQperm (Equiv.swap (0 : Fin 3) 2) g₁ g_bg,
    hQperm (finRotate 3) g₁ g₁, hQperm (finRotate 3) g₁ g_bg]
  rw [hswap0, hswap1, hswap2, hrot0, hrot1, hrot2]
  rw [dLaCovKernel_backgroundSplit (I := I) g₀ g₁ g_bg x (w 0) (w 1) (w 2)]
  have hcocy : ∀ u v : TangentSpace I x,
      PDE.DeTurck.connDiff (I := I) g₁ g_bg x u v =
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x u v -
          PDE.DeTurck.connDiff (I := I) g_bg g₀ x u v :=
    fun u v => eq_sub_of_add_eq (connDiff_cocycle (I := I) g₁ g_bg g₀ x u v)
  rw [hcocy (w 1) (w 2)]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 2) -
        PDE.DeTurck.connDiff (I := I) g_bg g₀ x (w 1) (w 2)) (w 0) =
      PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 2)) (w 0) -
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g_bg g₀ x (w 1) (w 2)) (w 0) from by
    rw [map_sub]
    rfl]
  rw [hcocy (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 0)) (w 2)]
  rw [show PDE.DeTurck.connDiff (I := I) g₁ g_bg x (w 1)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0)) =
      PDE.DeTurck.connDiff (I := I) g₁ g_bg x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0)) (w 1) from
    PDE.DeTurck.connDiff_symm (I := I) g₁ g_bg x (w 1)
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0))]
  rw [hcocy (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 2) (w 0)) (w 1)]
  rw [cotangentToDual_map_sub_dla, cotangentToDual_map_sub_dla, cotangentToDual_map_add_dla,
    cotangentToDual_map_sub_dla, cotangentToDual_map_sub_dla, cotangentToDual_map_sub_dla,
    cotangentToDual_map_sub_dla]
  ring

set_option backward.isDefEq.respectTransparency false in
private noncomputable def dLaPerturbSharpEndoFib (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => metricSharp (I := I) g₀ x
        (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap
      map_add' := fun v v' => by
        have h : ((ccTensorBilinSymm (I := I) g₀ T x (v + v')).toLinearMap) =
            (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap +
              (ccTensorBilinSymm (I := I) g₀ T x v').toLinearMap := by
          ext w
          simp [map_add]
        rw [show metricSharp (I := I) g₀ x
            (ccTensorBilinSymm (I := I) g₀ T x (v + v')).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ccTensorBilinSymm (I := I) g₀ T x (v + v')).toLinearMap from rfl,
          h, map_add]
        rfl
      map_smul' := fun c v => by
        have h : ((ccTensorBilinSymm (I := I) g₀ T x (c • v)).toLinearMap) =
            c • (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap := by
          ext w
          simp [map_smul]
        rw [show metricSharp (I := I) g₀ x
            (ccTensorBilinSymm (I := I) g₀ T x (c • v)).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ccTensorBilinSymm (I := I) g₀ T x (c • v)).toLinearMap from rfl,
          h, map_smul]
        rfl }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma dLaPerturbSharpEndoFib_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v : TangentSpace I x) :
    dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x v =
      metricSharp (I := I) g₀ x (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap := by
  rw [dLaPerturbSharpEndoFib, LinearMap.coe_toContinuousLinearMap']
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma inner_dLaPerturbSharpEndoFib (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    g₀.inner x (dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x v) w =
      ccTensorBilinSymm (I := I) g₀ T x v w := by
  rw [dLaPerturbSharpEndoFib_apply]
  exact inner_metricSharp (I := I) g₀ x
    (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap w

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] in
private theorem dLaPerturbSharpEndoFib_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x)) := by
  apply cotangentCov_clmSection_smooth_aux (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (ccTensorBilinSymm (I := I) g₀ T b (Y b)).toLinearMap
          (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have hB : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
          (ccTensorBilinSymm (I := I) g₀ T b)) :=
      ccTensorBilinSymm_contMDiff (I := I) g₀ T
    have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (chartBasisVec (I := I) α j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartBasisVec_contMDiffOn (I := I) α j
    have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b,
            ccTensorBilinSymm (I := I) g₀ T b (Y b) (chartBasisVecFiber (I := I) α j b)⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := id) hB.contMDiffOn Y.contMDiff.contMDiffOn hBasis
    have hbase_eq :
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) α
    rw [hbase_eq] at happ
    intro b hb
    have hpb := happ b hb
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
    exact hpb.2
  have hsmooth := metricSharp_contMDiff_total (I := I) g₀
    (cv := fun b : M => (ccTensorBilinSymm (I := I) g₀ T b (Y b)).toLinearMap) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (metricSharp (I := I) g₀ x (ccTensorBilinSymm (I := I) g₀ T x (Y x)).toLinearMap) =
    TotalSpace.mk' E x (dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x (Y x))
  rw [dLaPerturbSharpEndoFib_apply]

private noncomputable def dLaPerturbSharpEndoField (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x
  contMDiff_toFun := dLaPerturbSharpEndoFib_contMDiff (I := I) (M := M) g₀ T

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_eq_ccTensorBilin_dla (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = smoothCcTensorBilinForm (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] in
private lemma dLaSlotInsert_perturbSharp_eq_raise_symmS (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T) =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g₀ T)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T)).toSection x) om) w =
      ccTensorBilinSymm (I := I) g₀ T x (w 0)
        (inverseMetricSharpFib (I := I) g₀ x om) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T)).toSection x) om) =
        slotInsertEndoFib (I := I) (M := M) 1 0 x
          (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x) om from rfl]
    rw [slotInsertEndoFib_apply_eval]
    rw [toModel_om_single_eq_cotangentToDual_dla (I := I) (M := M) x om
      (Function.update w 0 (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (w 0)))]
    rw [Function.update_self]
    rw [show (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x) =
        dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x from rfl]
    rw [cotangentToDual_eq_inner_sharp_dla (I := I) (M := M) g₀ x om
      (dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x (w 0))]
    rw [inner_dLaPerturbSharpEndoFib]
  rw [hLHS]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
            (ccTensor02Symm (I := I) (M := M) g₀ T))).toSection x) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        cometricRaiseSlot0Fib g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)
            (unitTensor (I := I) (M := M) x))) om) from rfl]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [interiorProduct_toModel_eval_dla (I := I) (M := M) 1 x
    (inverseMetricSharpFib (I := I) g₀ x om) _ w]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (ccTensor02Symm (I := I) (M := M) g₀ T)) x from rfl]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
    (ccTensor02Symm (I := I) (M := M) g₀ T) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 2 =>
      (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 2 → E) ((Equiv.swap (0 : Fin 2) 1) i)) =
      (![(w 0 : E), (show E from inverseMetricSharpFib (I := I) g₀ x om)] : Fin 2 → E) from by
    funext i
    fin_cases i <;> rfl]
  rw [unitModel_eq_ccTensorBilin_dla (I := I) (M := M) g₀ (ccTensor02Symm (I := I) (M := M) g₀ T) x
    (w 0) (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T x]

private noncomputable def dLaLoweredPerturbCc (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 4 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 0 4 4
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3 (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))
    (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)

private noncomputable def dLaLoweredG1Cc (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 4 :=
  dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg +
    dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_add_dla (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : SmoothCcTensor g₀ 0 s) (x : M) (m : Fin s → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ s (A + B) x m =
      unitModel (I := I) (M := M) g₀ s A x m + unitModel (I := I) (M := M) g₀ s B x m := by
  rw [unitModel, unitModel, unitModel]
  rw [show ((A + B).toSection x) = A.toSection x + B.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      (A.toSection x + B.toSection x)) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A.toSection x)
          (unitTensor (I := I) (M := M) x) +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B.toSection x)
          (unitTensor (I := I) (M := M) x) from rfl]
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma dLaLoweredPerturbCc_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg) x m =
      ccTensorBilinSymm (I := I) g₀ T x
        (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) := by
  have hsec : unitModel (I := I) (M := M) g₀ 4
      (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg) x m =
      Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) 4 0 x
          (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x))) m := by
    rw [unitModel]
    rw [show ((dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg).toSection x)
        (unitTensor (I := I) (M := M) x) =
        slotInsertEndoFib (I := I) (M := M) 4 0 x
          (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
            (unitTensor (I := I) (M := M) x)) from by
      rw [dLaLoweredPerturbCc, appCcRS_toSection]
      rfl]
  rw [hsec]
  rw [slotInsertEndoFib_apply_eval]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
        (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 4 (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x from rfl]
  rw [dLaLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x]
  rw [show (Function.update m 0
      (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0))) 0 =
      dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0) from Function.update_self _ _ _]
  rw [show (Function.update m 0
      (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0))) 1 = m 1 from
    Function.update_of_ne (by decide) _ _]
  rw [show (Function.update m 0
      (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0))) 2 = m 2 from
    Function.update_of_ne (by decide) _ _]
  rw [show (Function.update m 0
      (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0))) 3 = m 3 from
    Function.update_of_ne (by decide) _ _]
  rw [g₀.symm x (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3))
    (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x (m 0))]
  rw [show (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T x) =
      dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x from rfl]
  rw [inner_dLaPerturbSharpEndoFib (I := I) (M := M) g₀ T x (m 0)
    (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3))]
  exact ccTensorBilinSymm_symm (I := I) g₀ T x (m 0)
    (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rfns_neg_dla (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (-v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_neg]
  rw [← neg_one_smul ℝ (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (r := r) (s := s) (x := x) v),
    tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rfns_smul_dla (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left, tensorInnerPointwise_smul_right]
  ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rfns_iCG_sub_le_dla (g : SmoothRiemannianMetric I M) (r s : ℕ) (j : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
        ((iteratedCovGrad (I := I) g r s j (A - B)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j A).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j B).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g r s j (A - B)).toSection x =
      (iteratedCovGrad (I := I) g r s j A).toSection x +
        (-(iteratedCovGrad (I := I) g r s j B).toSection x) := by
    rw [sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_neg, SmoothCcTensor.toSection_add]
    rw [show ((iteratedCovGrad (I := I) g r s j A).toSection +
        (-iteratedCovGrad (I := I) g r s j B).toSection) x =
        (iteratedCovGrad (I := I) g r s j A).toSection x +
          (-iteratedCovGrad (I := I) g r s j B).toSection x from rfl]
    rw [SmoothCcTensor.toSection_neg]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + j) x _ _) ?_
  rw [rfns_neg_dla (I := I) (M := M) g r (s + j) x]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma rfns_iCG_add_le_dla (g : SmoothRiemannianMetric I M) (r s : ℕ) (j : ℕ)
    (A B : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
        ((iteratedCovGrad (I := I) g r s j (A + B)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j A).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j B).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g r s j (A + B)).toSection x =
      (iteratedCovGrad (I := I) g r s j A).toSection x +
        (iteratedCovGrad (I := I) g r s j B).toSection x := by
    rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g r (s + j) x _ _

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem exists_fixedField_rfns_jet_dla (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (F : SmoothCcTensor g₀ r s) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ ∀ (j : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c j := by
  have hex : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + j) x
        ((iteratedCovGrad (I := I) g₀ r s j F).toSection x) ≤ c :=
    fun j => exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ r (s + j)
      (iteratedCovGrad (I := I) g₀ r s j F)
  choose c hc_nn hc using hex
  exact ⟨c, hc_nn, fun j x => hc j x⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma g1_inner_gInvRaisedEndo_left_dla (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
  rw [gInvRaisedEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
  rw [show cotangentToDualLinear (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w from rfl]
  rw [cotangentToDual_g0FlatCLM]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma g0_inner_inverseMetricSharp_mixed_dla (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (v : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₁ x om) v =
      cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) := by
  rw [show cotangentToDual (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) =
      cotangentToDualLinear (I := I) (x := x) om (metricComparisonEndo (I := I) g₀ g₁ x v) from rfl]
  rw [← inverseMetricSharpFib_inner (I := I) g₁ x om (metricComparisonEndo (I := I) g₀ g₁ x v)]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om) (metricComparisonEndo (I := I) g₀ g₁ x v)]
  rw [g1_inner_gInvRaisedEndo_left_dla (I := I) (M := M) g₀ g₁ x v
    (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [g₀.symm x v (inverseMetricSharpFib (I := I) g₁ x om)]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma sharpFlatEndoCc_eq_slotInsert_fullRaised_dla (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om) =
      (g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) om) =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) om from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [toModel_om_single_eq_cotangentToDual_dla (I := I) (M := M) x om
    (Function.update m 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x (m 0)))]
  rw [Function.update_self]
  rw [toModel_om_single_eq_cotangentToDual_dla (I := I) (M := M) x
    ((g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om)) m]
  rw [cotangentToDual_g0FlatCLM]
  rw [g0_inner_inverseMetricSharp_mixed_dla (I := I) (M := M) g₀ g₁ x om (m 0)]
  rw [fullRaisedEndoField_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma fullRaisedEndoField_diff_split_dla (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) = metricComparisonDiffEndo (I := I) g₀ g₁ x
    from rfl]
  rw [fullRaisedEndoField_apply]
  rw [gInvRaisedEndo_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show metricComparisonEndo (I := I) g₀ g₀ x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotInsertEndoCc_add_endo_dla (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ s (A + B) =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ s A +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ s A +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x) =
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ s A).toSection x +
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma endoCovariantDerivative_fullRaised_id_eq_zero_dla (g₀ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x v) (Y x) = 0 := by
  have hLeib := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀) Y x v
  have hΛapp : (fun y : M => (fullRaisedEndoField (I := I) (M := M) g₀ g₀ y) (Y y)) =
      (fun y : M => Y y) := by
    funext y
    rw [fullRaisedEndoField_apply]
    rw [show metricComparisonEndo (I := I) g₀ g₀ y (Y y) = Y y from by
      rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [hLeib, hΛapp]
  rw [fullRaisedEndoField_apply]
  rw [show metricComparisonEndo (I := I) g₀ g₀ x
      ((LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v) =
      (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [sub_self]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covGrad_slotInsert_fullRaised_id_eq_zero_dla (g₀ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 1 1
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) x D m]
  rw [tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ 0
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)]
  rw [show ((endoCovariantDerivative (I := I) (M := M) g₀)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)) =
      (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from by
    apply ContinuousLinearMap.ext
    intro w
    rw [ContinuousLinearMap.zero_apply]
    obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x w
    rw [← hY]
    exact endoCovariantDerivative_fullRaised_id_eq_zero_dla (I := I) (M := M) g₀ Y x (m 0)]
  rw [show slotInsertEndoFib (I := I) (M := M) (0 + 1) 0 x
        (0 : TangentSpace I x →L[ℝ] TangentSpace I x) = 0 from by
    rw [show (0 : TangentSpace I x →L[ℝ] TangentSpace I x) =
        (0 : ℝ) • (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from (zero_smul ℝ _).symm,
      slotInsertEndoFib_smul_left, zero_smul]]
  simp [SmoothCcTensor.toSection_zero]

omit [NeZero (Module.finrank ℝ E)] in
private lemma iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero_dla
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact covGrad_slotInsert_fullRaised_id_eq_zero_dla (I := I) (M := M) g₀
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

private theorem exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid_dla
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ S : ℕ → ℝ, (∀ l, 0 ≤ S l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          S l * Combinatorics.antidiagonalTupleGrid
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) l := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cid, hcid_nn, hcid⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 1 1
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₀))
  refine ⟨fun l => 2 * CD l + 2 * cid,
    fun l => by have := hCD_nn l; linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b l :=
    Combinatorics.antidiagonalTupleGrid_nonneg b hb l
  have hsplit : sharpFlatEndoCc (I := I) g₀ g₁ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁) +
        endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀) := by
    rw [sharpFlatEndoCc_eq_slotInsert_fullRaised_dla (I := I) (M := M) g₀ g₁,
      fullRaisedEndoField_diff_split_dla (I := I) (M := M) g₀ g₁,
      slotInsertEndoCc_add_endo_dla (I := I) (M := M) g₀ 0]
  have hsec : (iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x =
      (iteratedCovGrad (I := I) g₀ 1 1 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x +
      (iteratedCovGrad (I := I) g₀ 1 1 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x := by
    rw [hsplit, iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + l) x _ _) ?_
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
      CD l * Combinatorics.antidiagonalTupleGrid b l :=
    hCD g₁ T htie hδ_le hδ0 hbound l x
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x) ≤
      cid * Combinatorics.antidiagonalTupleGrid b l := by
    match l with
    | 0 =>
        rw [iteratedCovGrad_zero]
        rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one]
        exact hcid x
    | (m + 1) =>
        rw [iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero_dla (I := I) (M := M) g₀ m]
        rw [show ((0 : SmoothCcTensor g₀ 1 (1 + (m + 1))).toSection x) =
            (0 : TensorRSSpace 1 (1 + (m + 1)) I x) from by
          rw [SmoothCcTensor.toSection_zero]; rfl]
        rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 1 (1 + (m + 1)) x]
        exact mul_nonneg hcid_nn
          (Combinatorics.antidiagonalTupleGrid_nonneg b hb (m + 1))
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x)
      ≤ 2 * (CD l * Combinatorics.antidiagonalTupleGrid b l) +
          2 * (cid * Combinatorics.antidiagonalTupleGrid b l) := by
        have h1 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
        linarith
    _ = (2 * CD l + 2 * cid) * Combinatorics.antidiagonalTupleGrid b l := by ring

private theorem exists_rfns_iteratedCovGrad_connDiffSection_tgrid_dla
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ CA : ℕ → ℝ, (∀ j, 0 ≤ CA j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j
              (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
          CA j * antidiagonalTupleGridPartialSum
            (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
              ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) (j + 2) := by
  classical
  obtain ⟨S, hS_nn, hS⟩ := exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid_dla
    (I := I) (M := M) g₀ hδ₀
  refine ⟨fun j => diagonalGridGrowthFactor (E := E) j *
      ∑ i ∈ Finset.range (j + 1), 10 * ∑ l ∈ Finset.range (j + 1 - i), S l,
    fun j => mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (Finset.sum_nonneg fun i _ => mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun l _ => hS_nn l)), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
    ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x) with hb_def
  have hb : ∀ j', 0 ≤ b j' :=
    fun j' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j') x _
  set G : ℝ := antidiagonalTupleGridPartialSum b (j + 2) with hG_def
  have hG_nn : 0 ≤ G := dLaGridWin_nonneg b hb (j + 2)
  have hcell : ∀ i ∈ Finset.range (j + 1), ∀ l ∈ Finset.range (j + 1 - i),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
      (10 * S l) * G := by
    intro i hi l hl
    have h1 := rfns_iteratedCovGrad_raisedKoszul_pointwise_le (I := I) (M := M) g₀ g₁ T htie i x
    have h2 := hS g₁ T htie hδ_le hδ0 hbound l x
    have h1_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
    have h2_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
    have hb_le_grid : b (i + 1) * Combinatorics.antidiagonalTupleGrid b l ≤
        Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) :=
      Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb l (i + 1) (by omega)
    have hgrid_le_G : Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) ≤ G := by
      rw [hG_def]
      refine grid_le_dLaGridWin b hb ?_
      rw [Finset.mem_range] at hi hl
      omega
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
        ≤ (10 * b (i + 1)) * (S l * Combinatorics.antidiagonalTupleGrid b l) :=
          mul_le_mul h1 h2 h2_nn (by
            have := hb (i + 1)
            positivity)
      _ = (10 * S l) * (b (i + 1) * Combinatorics.antidiagonalTupleGrid b l) := by ring
      _ ≤ (10 * S l) * Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) := by
          refine mul_le_mul_of_nonneg_left hb_le_grid ?_
          have := hS_nn l
          positivity
      _ ≤ (10 * S l) * G := by
          refine mul_le_mul_of_nonneg_left hgrid_le_G ?_
          have := hS_nn l
          positivity
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_connDiffSection_diagonalProductGrid_le
    (I := I) (M := M) g₀ g₁ j x) ?_
  have hsum : ∑ i ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
      ∑ i ∈ Finset.range (j + 1), (10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mul_sum]
    have hrw : (10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G =
        ∑ l ∈ Finset.range (j + 1 - i), (10 * S l) * G := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hrw]
    exact Finset.sum_le_sum fun l hl => hcell i hi l hl
  refine le_trans (mul_le_mul_of_nonneg_left hsum (appCcGdiag_nonneg (E := E) j)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma connDiffSection_eq_armSlotEndoCc_zero_dla (g₀ gc : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) gc g₀ =
      armSlotEndoCc (I := I) (M := M) g₀ 0 (dLaConnArmPt (I := I) (M := M) g₀ gc) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (armSlotEndoCc (I := I) (M := M) g₀ 0
          (dLaConnArmPt (I := I) (M := M) g₀ gc)).toSection x) om) =
      bilinearSlotInsertCLM (I := I) (M := M) 0 x (dLaConnArmPt (I := I) (M := M) g₀ gc x) om
      from rfl]
  rw [armSlotFib_apply_eval (I := I) (M := M) 0 x
    (dLaConnArmPt (I := I) (M := M) g₀ gc x) om v]
  rw [slotInsertEndoFib_apply_eval]
  rw [show (Function.update (Matrix.vecTail (fun k : Fin 2 => (v k : E))) 0
        (dLaConnArmPt (I := I) (M := M) g₀ gc x (v 0)
          (Matrix.vecTail (fun k : Fin 2 => (v k : E)) 0))) =
      (fun _ : Fin 1 => (show E from
        PDE.DeTurck.connDiff (I := I) gc g₀ x (v 0) (v 1))) from by
    funext k
    rw [show k = (0 : Fin 1) from Subsingleton.elim k 0]
    rw [Function.update_self]
    rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) gc g₀).toSection x) om) =
      connDiffPairing (I := I) gc g₀ x om from rfl]
  change connDiffPairing (I := I) gc g₀ x om v = _
  rw [connDiffPairing_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma armSlotEndoCc_one_eq_reindex_slotExtend_dla (g₀ : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    armSlotEndoCc (I := I) (M := M) g₀ 1 Arm =
      reindexCoeffGen (I := I) (M := M) g₀ 2 3
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
          (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
        (Equiv.swap (0 : Fin 2) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hτ0 : (finRotate 3).symm (0 : Fin 3) = (2 : Fin 3) := by decide
  have hτ1 : (finRotate 3).symm (1 : Fin 3) = (0 : Fin 3) := by decide
  have hτ2 : (finRotate 3).symm (2 : Fin 3) = (1 : Fin 3) := by decide
  set D' : Tensor0SSpace 2 I x := Tensor0SSpace.ofModel
    (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
      (Tensor0SSpace.toModel D)) with hD'_def
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm).toSection x) D) w =
      Tensor0SSpace.toModel D
        (Function.update (Matrix.vecTail w) 0 (Arm x (w 0) (Matrix.vecTail w 0))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm).toSection x) D) =
        bilinearSlotInsertCLM (I := I) (M := M) 1 x (Arm x) D from rfl]
    rw [armSlotFib_apply_eval (I := I) (M := M) 1 x (Arm x) D w]
    rw [slotInsertEndoFib_apply_eval]
  have e1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 3
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) w =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          tensorRS_domDomCongr (finRotate 3).symm
            ((slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') w := by
    have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 3
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          tensorRS_domDomCongr (finRotate 3).symm
            ((slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') := by
      rw [reindexCoeffGen_toSection]
      rw [reindexCoeffFibGen_apply (I := I) 2 3 (Equiv.swap (0 : Fin 2) 1) x
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm))).toSection x) D]
      rw [← hD'_def]
      rw [rsDomDomCongrSection_toSection]
    exact congrArg (fun t : Tensor0SSpace 3 I x => Tensor0SSpace.toModel t w) h1
  have e2 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        tensorRS_domDomCongr (finRotate 3).symm
          ((slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') w =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D')
        (fun i => w ((finRotate 3).symm i)) := by
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (finRotate 3).symm
      ((slotExtend (I := I) (M := M) g₀ 1 2
        (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D']
    rw [ContinuousMultilinearMap.domDomCongr_apply]
  have e3 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotExtend (I := I) (M := M) g₀ 1 2
          (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D')
      (fun i => w ((finRotate 3).symm i)) =
      Tensor0SSpace.toModel
        (bilinearSlotInsertCLM (I := I) (M := M) 0 x (Arm x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0))))
        (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D') =
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x).symm
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm).toSection x).comp
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D')) from rfl]
    rw [show (fun i => w ((finRotate 3).symm i)) =
        Fin.cons (w ((finRotate 3).symm 0))
          (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) from by
      funext k
      refine Fin.cases rfl (fun j => rfl) k]
    have hkey := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2)
      (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D')))
      (v0 := w ((finRotate 3).symm 0))
      (vs := Matrix.vecTail (fun i => w ((finRotate 3).symm i)))
    rw [ContinuousLinearEquiv.apply_symm_apply] at hkey
    rw [← hkey]
    rfl
  have e4 : Tensor0SSpace.toModel
      (bilinearSlotInsertCLM (I := I) (M := M) 0 x (Arm x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0))))
      (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
        (fun _ : Fin 1 => (show E from
          Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2)))) := by
    rw [armSlotFib_apply_eval (I := I) (M := M) 0 x (Arm x)
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
      (Matrix.vecTail (fun i => w ((finRotate 3).symm i)))]
    rw [slotInsertEndoFib_apply_eval]
    congr 1
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [Function.update_self]
    rfl
  have e5 : Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
      (fun _ : Fin 1 => (show E from
        Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2)))) =
      Tensor0SSpace.toModel D'
        (Fin.cons (w ((finRotate 3).symm 0))
          (fun _ : Fin 1 => (show E from
            Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))) :=
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D') (v0 := w ((finRotate 3).symm 0))
      (vs := fun _ : Fin 1 => (show E from
        Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))
  have e6 : Tensor0SSpace.toModel D'
      (Fin.cons (w ((finRotate 3).symm 0))
        (fun _ : Fin 1 => (show E from
          Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))) =
      Tensor0SSpace.toModel D
        (Function.update (Matrix.vecTail w) 0 (Arm x (w 0) (Matrix.vecTail w 0))) := by
    rw [hD'_def, Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [hτ0, hτ1, hτ2]
    congr 1
    funext k
    refine Fin.cases ?_ ?_ k
    · rw [show (Function.update (Matrix.vecTail w) 0
            (Arm x (w 0) (Matrix.vecTail w 0)) (0 : Fin 2)) =
          Arm x (w 0) (Matrix.vecTail w 0) from Function.update_self _ _ _]
      rfl
    · intro j
      refine Fin.cases ?_ (fun j2 => j2.elim0) j
      rw [show (Fin.succ (0 : Fin 1)) = (1 : Fin 2) from rfl]
      rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      rfl
  rw [hLHS, e1, e2, e3, e4, e5, e6]

private lemma rfns_iteratedCovGrad_armSlotPass_connArm_le_dla
    (g₀ gc : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 3 j
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (dLaConnArmPt (I := I) (M := M) g₀ gc))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) gc g₀)).toSection x) := by
  rw [riemannianFiberNormSq_iteratedCovGrad_armSlotEndoPassZeroCc_eq (I := I) (M := M) g₀
    (dLaConnArmPt (I := I) (M := M) g₀ gc) j x]
  rw [armSlotEndoCc_one_eq_reindex_slotExtend_dla (I := I) (M := M) g₀
    (dLaConnArmPt (I := I) (M := M) g₀ gc)]
  rw [rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 3
    (Equiv.swap (0 : Fin 2) 1) (finRotate 3).symm
    (slotExtend (I := I) (M := M) g₀ 1 2
      (armSlotEndoCc (I := I) (M := M) g₀ 0 (dLaConnArmPt (I := I) (M := M) g₀ gc))) j x]
  refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
    (armSlotEndoCc (I := I) (M := M) g₀ 0 (dLaConnArmPt (I := I) (M := M) g₀ gc)) j x) ?_
  rw [← connDiffSection_eq_armSlotEndoCc_zero_dla (I := I) (M := M) g₀ gc]

private lemma dLaQuad_tower_of_factors (g₀ ga gb : SmoothRiemannianMetric I M)
    (j : ℕ) (x : M) (b : ℕ → ℝ) (hb : ∀ l, 0 ≤ b l)
    (Ba Bb : ℕ → ℝ) (hBa_nn : ∀ i, 0 ≤ Ba i) (hBb_nn : ∀ l, 0 ≤ Bb l)
    (harm : ∀ i, i ≤ j →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) ga g₀)).toSection x) ≤
      Ba i * antidiagonalTupleGridPartialSum b (i + 2))
    (hin : ∀ l, l ≤ j →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 2 l (connDiffSection (I := I) gb g₀)).toSection x) ≤
      Bb l * antidiagonalTupleGridPartialSum b (l + 2)) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 3 j
          (dLaQuadCc (I := I) (M := M) g₀ ga gb)).toSection x) ≤
      (diagonalGridGrowthFactor (E := E) j * ∑ i ∈ Finset.range (j + 1),
        (Module.finrank ℝ E : ℝ) * Ba i *
          ∑ l ∈ Finset.range (j + 1 - i), Bb l * antidiagonalTuplePairCount (i + 2) (l + 2)) *
        antidiagonalTupleGridPartialSum b (j + 3) := by
  have hWnn : 0 ≤ antidiagonalTupleGridPartialSum b (j + 3) := dLaGridWin_nonneg b hb (j + 3)
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ j 1 2 3
    (armSlotEndoPassZeroCc (I := I) (M := M) g₀ (dLaConnArmPt (I := I) (M := M) g₀ ga))
    (connDiffSection (I := I) gb g₀) x) ?_
  have hcell : ∀ i ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 3 i
            (armSlotEndoPassZeroCc (I := I) (M := M) g₀
              (dLaConnArmPt (I := I) (M := M) g₀ ga))).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l
              (connDiffSection (I := I) gb g₀)).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * Ba i *
        ∑ l ∈ Finset.range (j + 1 - i), Bb l * antidiagonalTuplePairCount (i + 2) (l + 2)) *
        antidiagonalTupleGridPartialSum b (j + 3) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hi_le : i ≤ j := by omega
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 3 i
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (dLaConnArmPt (I := I) (M := M) g₀ ga))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) * (Ba i * antidiagonalTupleGridPartialSum b (i + 2)) := by
      refine le_trans (rfns_iteratedCovGrad_armSlotPass_connArm_le_dla
        (I := I) (M := M) g₀ ga i x) ?_
      exact mul_le_mul_of_nonneg_left (harm i hi_le) hfr_nn
    have hA2 : (∑ l ∈ Finset.range (j + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connDiffSection (I := I) gb g₀)).toSection x)) ≤
        ∑ l ∈ Finset.range (j + 1 - i), Bb l * antidiagonalTupleGridPartialSum b (l + 2) := by
      refine Finset.sum_le_sum fun l hl => ?_
      rw [Finset.mem_range] at hl
      exact hin l (by omega)
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connDiffSection (I := I) gb g₀)).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + l) x _
    have hA1_rhs_nn : 0 ≤ (Module.finrank ℝ E : ℝ) * (Ba i * antidiagonalTupleGridPartialSum b (i + 2)) :=
      mul_nonneg hfr_nn (mul_nonneg (hBa_nn i) (dLaGridWin_nonneg b hb (i + 2)))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show ((Module.finrank ℝ E : ℝ) * Ba i *
        ∑ l ∈ Finset.range (j + 1 - i), Bb l * antidiagonalTuplePairCount (i + 2) (l + 2)) *
        antidiagonalTupleGridPartialSum b (j + 3) =
        ∑ l ∈ Finset.range (j + 1 - i),
          ((Module.finrank ℝ E : ℝ) * Ba i * (Bb l * antidiagonalTuplePairCount (i + 2) (l + 2))) *
            antidiagonalTupleGridPartialSum b (j + 3) from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : antidiagonalTupleGridPartialSum b (i + 2) * antidiagonalTupleGridPartialSum b (l + 2) ≤
        antidiagonalTuplePairCount (i + 2) (l + 2) * antidiagonalTupleGridPartialSum b (j + 3) :=
      dLaGridWin_mul_le b hb (i + 2) (l + 2) (j + 3) (by omega)
    calc (Module.finrank ℝ E : ℝ) * (Ba i * antidiagonalTupleGridPartialSum b (i + 2)) *
          (Bb l * antidiagonalTupleGridPartialSum b (l + 2))
        = ((Module.finrank ℝ E : ℝ) * Ba i * Bb l) *
            (antidiagonalTupleGridPartialSum b (i + 2) * antidiagonalTupleGridPartialSum b (l + 2)) := by ring
      _ ≤ ((Module.finrank ℝ E : ℝ) * Ba i * Bb l) *
            (antidiagonalTuplePairCount (i + 2) (l + 2) * antidiagonalTupleGridPartialSum b (j + 3)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (mul_nonneg hfr_nn (hBa_nn i)) (hBb_nn l)
      _ = (Module.finrank ℝ E : ℝ) * Ba i * (Bb l * antidiagonalTuplePairCount (i + 2) (l + 2)) *
            antidiagonalTupleGridPartialSum b (j + 3) := by ring
  calc diagonalGridGrowthFactor (E := E) j *
        ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 3 i
                (armSlotEndoPassZeroCc (I := I) (M := M) g₀
                  (dLaConnArmPt (I := I) (M := M) g₀ ga))).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 2 l
                  (connDiffSection (I := I) gb g₀)).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) j *
          ∑ i ∈ Finset.range (j + 1),
            ((Module.finrank ℝ E : ℝ) * Ba i *
              ∑ l ∈ Finset.range (j + 1 - i), Bb l * antidiagonalTuplePairCount (i + 2) (l + 2)) *
              antidiagonalTupleGridPartialSum b (j + 3) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) j)
    _ = (diagonalGridGrowthFactor (E := E) j * ∑ i ∈ Finset.range (j + 1),
          (Module.finrank ℝ E : ℝ) * Ba i *
            ∑ l ∈ Finset.range (j + 1 - i), Bb l * antidiagonalTuplePairCount (i + 2) (l + 2)) *
          antidiagonalTupleGridPartialSum b (j + 3) := by
        rw [← Finset.sum_mul, ← mul_assoc]

private theorem exists_rfns_dLaKernelRaised_tgrid (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 3 i
              (dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C i * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_rfns_iteratedCovGrad_connDiffSection_tgrid_dla
    (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_fixedField_rfns_jet_dla (I := I) (M := M) g₀ 1 3
    (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀))
  obtain ⟨cc, hcc_nn, hcc⟩ := exists_fixedField_rfns_jet_dla (I := I) (M := M) g₀ 1 2
    (connDiffSection (I := I) g_bg g₀)
  set CQ1 : ℕ → ℝ := fun j => diagonalGridGrowthFactor (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * CA i' *
      ∑ l ∈ Finset.range (j + 1 - i'), CA l * antidiagonalTuplePairCount (i' + 2) (l + 2) with hCQ1_def
  set CQ2 : ℕ → ℝ := fun j => diagonalGridGrowthFactor (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * cc i' *
      ∑ l ∈ Finset.range (j + 1 - i'), CA l * antidiagonalTuplePairCount (i' + 2) (l + 2) with hCQ2_def
  set CQ3 : ℕ → ℝ := fun j => diagonalGridGrowthFactor (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * CA i' *
      ∑ l ∈ Finset.range (j + 1 - i'), cc l * antidiagonalTuplePairCount (i' + 2) (l + 2) with hCQ3_def
  have hCQ1_nn : ∀ j, 0 ≤ CQ1 j := by
    intro j
    refine mul_nonneg (appCcGdiag_nonneg (E := E) j) (Finset.sum_nonneg fun i' _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn i'))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hCA_nn l) (dLaPairCount_nonneg _ _))
  have hCQ2_nn : ∀ j, 0 ≤ CQ2 j := by
    intro j
    refine mul_nonneg (appCcGdiag_nonneg (E := E) j) (Finset.sum_nonneg fun i' _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hcc_nn i'))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hCA_nn l) (dLaPairCount_nonneg _ _))
  have hCQ3_nn : ∀ j, 0 ≤ CQ3 j := by
    intro j
    refine mul_nonneg (appCcGdiag_nonneg (E := E) j) (Finset.sum_nonneg fun i' _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn i'))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hcc_nn l) (dLaPairCount_nonneg _ _))
  refine ⟨fun i => 2 * (2 * (2 * (2 * (2 * (2 * (2 * CA (i + 1) + 2 * cbg i) + 2 * CQ1 i)
      + 2 * CQ2 i) + 2 * CQ1 i) + 2 * CQ3 i) + 2 * CQ1 i) + 2 * CQ3 i,
    fun i => by
      have h1 := hCA_nn (i + 1)
      have h2 := hcbg_nn i
      have h3 := hCQ1_nn i
      have h4 := hCQ2_nn i
      have h5 := hCQ3_nn i
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := antidiagonalTupleGridPartialSum b (i + 3) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (i + 3)
  have hW_ge1 : 1 ≤ W := one_le_dLaGridWin b hb (by omega)
  have harm : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 2 i' (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      CA i' * antidiagonalTupleGridPartialSum b (i' + 2) :=
    fun i' _ => hCA g₁ T htie hδ_le hδ0 hbound i' x
  have hfix : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 2 i' (connDiffSection (I := I) g_bg g₀)).toSection x) ≤
      cc i' * antidiagonalTupleGridPartialSum b (i' + 2) := by
    intro i' _
    refine le_trans (hcc i' x) ?_
    have h1 : (1 : ℝ) ≤ antidiagonalTupleGridPartialSum b (i' + 2) := one_le_dLaGridWin b hb (by omega)
    nlinarith [hcc_nn i']
  have hQ1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g₁)).toSection x) ≤ CQ1 i * W :=
    dLaQuad_tower_of_factors (I := I) (M := M) g₀ g₁ g₁ i x b hb CA CA hCA_nn hCA_nn harm harm
  have hQ2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dLaQuadCc (I := I) (M := M) g₀ g_bg g₁)).toSection x) ≤ CQ2 i * W :=
    dLaQuad_tower_of_factors (I := I) (M := M) g₀ g_bg g₁ i x b hb cc CA hcc_nn hCA_nn hfix harm
  have hQ3 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ CQ3 i * W :=
    dLaQuad_tower_of_factors (I := I) (M := M) g₀ g₁ g_bg i x b hb CA cc hCA_nn hcc_nn harm hfix
  have hrs_eq : ∀ (σ : Equiv.Perm (Fin 3)) (F : SmoothCcTensor g₀ 1 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ F)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i F).toSection x) := by
    intro σ F
    exact riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 1 3 σ F
      (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ F)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x
  have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x) ≤
      CA (i + 1) * W := by
    rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 i
      (connDiffSection (I := I) g₁ g₀) x]
    exact hCA g₁ T htie hδ_le hδ0 hbound (i + 1) x
  have hA2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀))).toSection x) ≤
      cbg i * W := by
    refine le_trans (hcbg i x) ?_
    nlinarith [hcbg_nn i]
  set A1 := covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) with hA1_def
  set A2 := covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀) with hA2_def
  set Q11 := dLaQuadCc (I := I) (M := M) g₀ g₁ g₁ with hQ11_def
  set Qbg1 := dLaQuadCc (I := I) (M := M) g₀ g_bg g₁ with hQbg1_def
  set Q1bg := dLaQuadCc (I := I) (M := M) g₀ g₁ g_bg with hQ1bg_def
  set P1 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2) Q11
    with hP1_def
  set P2 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2) Q1bg
    with hP2_def
  set P3 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) Q11 with hP3_def
  set P4 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) Q1bg with hP4_def
  have hP1_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P1).toSection x) ≤ CQ1 i * W :=
    le_of_eq_of_le (hrs_eq (Equiv.swap (0 : Fin 3) 2) Q11) hQ1
  have hP2_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P2).toSection x) ≤ CQ3 i * W :=
    le_of_eq_of_le (hrs_eq (Equiv.swap (0 : Fin 3) 2) Q1bg) hQ3
  have hP3_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P3).toSection x) ≤ CQ1 i * W :=
    le_of_eq_of_le (hrs_eq (finRotate 3) Q11) hQ1
  have hP4_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P4).toSection x) ≤ CQ3 i * W :=
    le_of_eq_of_le (hrs_eq (finRotate 3) Q1bg) hQ3
  have t1 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i A1 A2 x
  have t2 := rfns_iCG_add_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2) Q11 x
  have t3 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11) Qbg1 x
  have t4 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11 - Qbg1) P1 x
  have t5 := rfns_iCG_add_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11 - Qbg1 - P1) P2 x
  have t6 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i
    (A1 - A2 + Q11 - Qbg1 - P1 + P2) P3 x
  have t7 := rfns_iCG_add_le_dla (I := I) (M := M) g₀ 1 3 i
    (A1 - A2 + Q11 - Qbg1 - P1 + P2 - P3) P4 x
  have hKK : dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg =
      A1 - A2 + Q11 - Qbg1 - P1 + P2 - P3 + P4 := rfl
  rw [hKK]
  linarith [t1, t2, t3, t4, t5, t6, t7, hA1, hA2, hQ1, hQ2, hQ3,
    hP1_le, hP2_le, hP3_le, hP4_le]

private theorem exists_rfns_dLaLowered_tgrid (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C i * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  obtain ⟨C, hC_nn, hC⟩ := exists_rfns_dLaKernelRaised_tgrid (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  have hbridge : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
    have h := riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 2
      (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) i x
    rw [dLaLoweredCc_raise_repr (I := I) (M := M) g₀ g₁ g_bg] at h
    exact h.symm
  rw [hbridge]
  exact hC g₁ T htie hδ_le hδ0 hbound i x

omit [NeZero (Module.finrank ℝ E)] in
private lemma rfns_iCG_symmS_le_dla (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x +
        (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 2 j
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x := by
    rw [iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ T j, SmoothCcTensor.toSection_add]
    rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j T).toSection +
        ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection) x =
        ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x +
          ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x from rfl]
    rw [SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_smul]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + j) x _ _) ?_
  rw [rfns_smul_dla (I := I) (M := M) g₀ 0 (2 + j) x, rfns_smul_dla (I := I) (M := M) g₀ 0 (2 + j) x]
  have hperm := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) T j x
  rw [hperm]
  ring_nf
  nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma rfns_symmS_zero_le_dla (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 0 2 x
    ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) e bse hnE hbse horth]
  have hcof : coframeS (I := I) (M := M) g₀ x 0 e = fun _ : Fin 0 → Fin n =>
      unitTensor (I := I) (M := M) x := by
    funext K
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 0 e K) v =
        coframeS (I := I) (M := M) g₀ x 0 e K v from rfl]
    rw [coframeS_apply (I := I) (M := M) g₀ x 0 e K v]
    rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) v =
        unitTensor (I := I) (M := M) x v from rfl]
    rw [Fin.prod_univ_zero]
    rw [unitTensor, Tensor0SSpace.ofModel]
    rfl
  have hcomp : ∀ (K : Fin 0 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2 ≤ δ ^ 2 := by
    intro K J
    have hval : fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) n e K J =
        ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)) := by
      rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) n e K J =
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
              (coframeS (I := I) (M := M) g₀ x 0 e K))
            (fun i : Fin 2 => (e (J i) : E)) from rfl]
      rw [hcof]
      rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
            (unitTensor (I := I) (M := M) x))
          (fun i : Fin 2 => (e (J i) : E)) =
          unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ T) x
            ![e (J 0), e (J 1)] from by
        rw [unitModel]
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
      rw [unitModel_eq_ccTensorBilin_dla (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T) x (e (J 0)) (e (J 1))]
      rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T x (e (J 0)) (e (J 1))]
    rw [hval]
    have habs := hbound x (e (J 0)) (e (J 1))
    have h00 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by
      rw [horth (J 0) (J 0), if_pos rfl]
    have h11 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by
      rw [horth (J 1) (J 1), if_pos rfl]
    rw [h00, h11, Real.sqrt_one, mul_one, mul_one] at habs
    have := abs_nonneg (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))
    nlinarith [habs, sq_abs (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))]
  calc (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2)
      ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, δ ^ 2 :=
        Finset.sum_le_sum fun K _ => Finset.sum_le_sum fun J _ => hcomp K J
    _ = (Fintype.card (Fin 0 → Fin n) : ℝ) * ((Fintype.card (Fin 2 → Fin n) : ℝ) * δ ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
        have hc0 : (Fintype.card (Fin 0 → Fin n) : ℝ) = 1 := by
          simp
        have hc2 : (Fintype.card (Fin 2 → Fin n) : ℝ) = (n : ℝ) ^ 2 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
        rw [hc0, hc2, one_mul, hnE]

private lemma rfns_iCG_slotInsert3_dLaPerturb_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + j) x
        ((iteratedCovGrad (I := I) g₀ 4 4 j
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
            (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) := by
  refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 3
    (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T) j x) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [dLaSlotInsert_perturbSharp_eq_raise_symmS (I := I) (M := M) g₀ T]
  rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
      (ccTensor02Symm (I := I) (M := M) g₀ T)) j x]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) (ccTensor02Symm (I := I) (M := M) g₀ T) j x]

private theorem exists_rfns_dLaSym_tgrid (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                  (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) +
                dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
          C i * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  classical
  obtain ⟨CL, hCL_nn, hCL⟩ := exists_rfns_dLaLowered_tgrid (I := I) (M := M) g₀ g_bg hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set CP : ℕ → ℝ := fun i' => fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) with hCP_def
  have hCP_nn : ∀ i', 0 ≤ CP i' := fun i' => by rw [hCP_def]; positivity
  set CLT : ℕ → ℝ := fun i => diagonalGridGrowthFactor (E := E) i * ∑ i' ∈ Finset.range (i + 1),
    CP i' * ∑ l ∈ Finset.range (i + 1 - i'), CL l * antidiagonalTuplePairCount (i' + 1) (l + 3) with hCLT_def
  have hCLT_nn : ∀ i, 0 ≤ CLT i := by
    intro i
    refine mul_nonneg (appCcGdiag_nonneg (E := E) i) (Finset.sum_nonneg fun i' _ => ?_)
    exact mul_nonneg (hCP_nn i') (Finset.sum_nonneg fun l _ =>
      mul_nonneg (hCL_nn l) (dLaPairCount_nonneg _ _))
  refine ⟨fun i => 4 * (2 * CL i + 2 * CLT i),
    fun i => by have := hCL_nn i; have := hCLT_nn i; positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := antidiagonalTupleGridPartialSum b (i + 3) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (i + 3)
  have hδ₀_nn : 0 ≤ δ₀ := le_trans hδ0 hδ_le
  have hPfac : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
        ((iteratedCovGrad (I := I) g₀ 4 4 i'
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
            (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤
      CP i' * antidiagonalTupleGridPartialSum b (i' + 1) := by
    intro i' _
    refine le_trans (rfns_iCG_slotInsert3_dLaPerturb_le (I := I) (M := M) g₀ T i' x) ?_
    have hfr3_nn : (0 : ℝ) ≤ fr ^ 3 := by positivity
    match i' with
    | 0 =>
        have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤ fr ^ 2 * δ ^ 2 := by
          rw [iteratedCovGrad_zero]
          exact rfns_symmS_zero_le_dla (I := I) (M := M) g₀ T hδ0 hbound x
        have hδsq : δ ^ 2 ≤ δ₀ ^ 2 := by nlinarith [hδ0, hδ_le]
        have hwin1 : (1 : ℝ) ≤ antidiagonalTupleGridPartialSum b (0 + 1) := one_le_dLaGridWin b hb (by omega)
        have hle1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤ fr ^ 2 * δ₀ ^ 2 := by
          refine le_trans h0 (mul_le_mul_of_nonneg_left hδsq (by positivity))
        calc fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
              ((iteratedCovGrad (I := I) g₀ 0 2 0
                (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)
            ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2) := mul_le_mul_of_nonneg_left hle1 hfr3_nn
          _ ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) := by
              refine mul_le_mul_of_nonneg_left ?_ hfr3_nn
              linarith
          _ ≤ (fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1)) * antidiagonalTupleGridPartialSum b (0 + 1) := by
              refine le_mul_of_one_le_right ?_ hwin1
              positivity
          _ = CP 0 * antidiagonalTupleGridPartialSum b (0 + 1) := by rw [hCP_def]
    | (m + 1) =>
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (m + 1)
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤ b (m + 1) :=
          rfns_iCG_symmS_le_dla (I := I) (M := M) g₀ T (m + 1) x
        have h2 : b (m + 1) ≤ Combinatorics.antidiagonalTupleGrid b (m + 1) :=
          single_le_grid_dla b hb (m + 1) (by omega)
        have h3 : Combinatorics.antidiagonalTupleGrid b (m + 1) ≤
            antidiagonalTupleGridPartialSum b ((m + 1) + 1) := grid_le_dLaGridWin b hb (by omega)
        have hfac1 : (1 : ℝ) ≤ fr ^ 2 * δ₀ ^ 2 + 1 :=
          le_add_of_nonneg_left (by positivity)
        have hwin_nn : 0 ≤ antidiagonalTupleGridPartialSum b ((m + 1) + 1) := dLaGridWin_nonneg b hb _
        calc fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (m + 1)
                (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)
            ≤ fr ^ 3 * antidiagonalTupleGridPartialSum b ((m + 1) + 1) := by
              refine mul_le_mul_of_nonneg_left ?_ hfr3_nn
              exact le_trans h1 (le_trans h2 h3)
          _ ≤ CP (m + 1) * antidiagonalTupleGridPartialSum b ((m + 1) + 1) := by
              rw [hCP_def]
              refine mul_le_mul_of_nonneg_right ?_ hwin_nn
              calc fr ^ 3 = fr ^ 3 * 1 := by ring
                _ ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) :=
                    mul_le_mul_of_nonneg_left hfac1 hfr3_nn
  have hLT : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      CLT i * W := by
    refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ i 0 4 4
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
        (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))
      (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x) ?_
    have hcell : ∀ i' ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
            ((iteratedCovGrad (I := I) g₀ 4 4 i'
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
          ∑ l ∈ Finset.range (i + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        (CP i' * ∑ l ∈ Finset.range (i + 1 - i'), CL l * antidiagonalTuplePairCount (i' + 1) (l + 3)) * W := by
      intro i' hi'
      rw [Finset.mem_range] at hi'
      have hi'_le : i' ≤ i := by omega
      have hA1 := hPfac i' hi'_le
      have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1 - i'), CL l * antidiagonalTupleGridPartialSum b (l + 3) :=
        Finset.sum_le_sum fun l _ => hCL g₁ T htie hδ_le hδ0 hbound l x
      have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _
      have hA1_rhs_nn : 0 ≤ CP i' * antidiagonalTupleGridPartialSum b (i' + 1) :=
        mul_nonneg (hCP_nn i') (dLaGridWin_nonneg b hb (i' + 1))
      refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
      rw [Finset.mul_sum]
      rw [show (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
          CL l * antidiagonalTuplePairCount (i' + 1) (l + 3)) * W =
          ∑ l ∈ Finset.range (i + 1 - i'),
            (CP i' * (CL l * antidiagonalTuplePairCount (i' + 1) (l + 3))) * W from by
        rw [Finset.mul_sum, Finset.sum_mul]]
      refine Finset.sum_le_sum fun l hl => ?_
      rw [Finset.mem_range] at hl
      have hpair : antidiagonalTupleGridPartialSum b (i' + 1) * antidiagonalTupleGridPartialSum b (l + 3) ≤
          antidiagonalTuplePairCount (i' + 1) (l + 3) * antidiagonalTupleGridPartialSum b (i + 3) :=
        dLaGridWin_mul_le b hb (i' + 1) (l + 3) (i + 3) (by omega)
      calc CP i' * antidiagonalTupleGridPartialSum b (i' + 1) * (CL l * antidiagonalTupleGridPartialSum b (l + 3))
          = (CP i' * CL l) * (antidiagonalTupleGridPartialSum b (i' + 1) * antidiagonalTupleGridPartialSum b (l + 3)) := by ring
        _ ≤ (CP i' * CL l) * (antidiagonalTuplePairCount (i' + 1) (l + 3) * antidiagonalTupleGridPartialSum b (i + 3)) := by
            refine mul_le_mul_of_nonneg_left hpair ?_
            exact mul_nonneg (hCP_nn i') (hCL_nn l)
        _ = (CP i' * (CL l * antidiagonalTuplePairCount (i' + 1) (l + 3))) * W := by
            rw [hW_def]
            ring
    calc diagonalGridGrowthFactor (E := E) i *
          ∑ i' ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
                ((iteratedCovGrad (I := I) g₀ 4 4 i'
                  (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                    (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
              ∑ l ∈ Finset.range (i + 1 - i'),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 l
                    (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        ≤ diagonalGridGrowthFactor (E := E) i *
            ∑ i' ∈ Finset.range (i + 1),
              (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
                CL l * antidiagonalTuplePairCount (i' + 1) (l + 3)) * W :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) i)
      _ = CLT i * W := by
          rw [hCLT_def, ← Finset.sum_mul, ← mul_assoc]
  have hL0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ CL i * W :=
    hCL g₁ T htie hδ_le hδ0 hbound i x
  have hLG1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      2 * (CL i * W) + 2 * (CLT i * W) := by
    refine le_trans (rfns_iCG_add_le_dla (I := I) (M := M) g₀ 0 4 i
      (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)
      (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg) x) ?_
    linarith [hL0, hLT]
  have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i
          (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 1) (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) i x
  refine le_trans (rfns_iCG_add_le_dla (I := I) (M := M) g₀ 0 4 i
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg))
    (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) x) ?_
  rw [hperm]
  linarith [hLG1]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma pureDTdla_eq_trace_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M)
    (s : ℕ) :
    cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ s =
      ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro Z
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro mm
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ s).toSection x) Z) mm =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ s).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₁ s x Z from rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ s x Z]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) (Tensor0SSpace.toModel Z) mm]
  rw [hLHS]
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) mm =
      ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from metricComparisonEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₀ s x
          (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z) from by
      rw [appCcRS_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ s x]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z)) mm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [slotInsertEndoFib_apply_eval]
    rw [Fin.update_cons_zero]
    rfl
  rw [hRHS]
  have hGrep : ∀ a : Fin (Module.finrank ℝ E),
      (show E from metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x)) =
        ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)) •
            (smoothOrthoFrame (I := I) g₁ x c x : E) := by
    intro a
    have h1 := smoothOrthoFrame_center_repr (I := I) (M := M) g₁ x
      (metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))
    rw [show (show E from metricComparisonEndo (I := I) g₀ g₁ x
        (smoothOrthoFrame (I := I) g₀ x a x)) =
        metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x) from rfl]
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x c x)
      (metricComparisonEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))]
    rw [g1_inner_gInvRaisedEndo_left_dla (I := I) (M := M) g₀ g₁ x
      (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)]
  symm
  calc (∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from metricComparisonEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)))
      = ∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hGrep a]
        exact toModel_cons_sum_smul_dla (E := E) x (Tensor0SSpace.toModel Z)
          (Module.finrank ℝ E)
          (fun c => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun c => (smoothOrthoFrame (I := I) g₁ x c x : E))
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)
    _ = ∑ c : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) :=
        Finset.sum_comm
    _ = ∑ c : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hsum := toModel_cons_cons_sum_smul_dla (E := E) x (Tensor0SSpace.toModel Z)
          ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
          (Module.finrank ℝ E)
          (fun a => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun a => (smoothOrthoFrame (I := I) g₀ x a x : E)) mm
        rw [← hsum]
        congr 2
        have hrep0 := smoothOrthoFrame_center_repr (I := I) (M := M) g₀ x
          (smoothOrthoFrame (I := I) g₁ x c x)
        rw [show (∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
              (smoothOrthoFrame (I := I) g₁ x c x) •
              (smoothOrthoFrame (I := I) g₀ x a x : E)) =
            ((∑ a : Fin (Module.finrank ℝ E),
              g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
                (smoothOrthoFrame (I := I) g₁ x c x) •
                smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) from rfl]
        rw [← hrep0]

private def pairTraceOpDla (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 6 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
    (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 2)
    (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 4)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma pairTraceOpDla_apply_toModel (g₀ gm : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (x : M) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ gm)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) v =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) gm x a x : E),
              (smoothOrthoFrame (I := I) gm x b x : E)] *
          unitModel (I := I) (M := M) g₀ 4 X x
            ![v 0, v 1, (smoothOrthoFrame (I := I) gm x a x : E),
              (smoothOrthoFrame (I := I) gm x b x : E)] := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 1, w 3] *
          unitModel (I := I) (M := M) g₀ 4 X x ![w 4, w 5, w 0, w 2] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRS_domDomCongr sigmaE0dla
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) sigmaE0dla
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendIter_two_toModel_dla (I := I) (M := M) g₀ X x D
      (fun i => w (sigmaE0dla i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ gm)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) =
      cometricDoubleTraceFib (I := I) gm 2 x
        (cometricDoubleTraceFib (I := I) gm 4 x Y) from by
    rw [hY_def]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) gm 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) gm x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) gm x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) gm 4 x Y))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cometricDoubleTraceFib_toModel (I := I) gm 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) gm x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) gm x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y)
    (Fin.cons ((smoothOrthoFrame (I := I) gm x b x : TangentSpace I x) : E)
      (Fin.cons ((smoothOrthoFrame (I := I) gm x b x : TangentSpace I x) : E)
        (fun j => (v j : E))))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hYval]
  rfl

private def dLaSymCc (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 :=
  domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) +
    dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma dLaLoweredG1Cc_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (g₁ g_bg : SmoothRiemannianMetric I M)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) x m =
      g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) := by
  rw [dLaLoweredG1Cc, unitModel_add_dla (I := I) (M := M) g₀ 4]
  rw [dLaLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₁ g_bg x m]
  rw [dLaLoweredPerturbCc_unitModel_apply (I := I) (M := M) g₀ T g₁ g_bg x m]
  rw [htie x (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0)]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma dLaSymCc_unitModel_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (g₁ g_bg : SmoothRiemannianMetric I M)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) x m =
      g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (m 0) (m 2) (m 3)) (m 1) +
        g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) := by
  rw [dLaSymCc, unitModel_add_dla (I := I) (M := M) g₀ 4]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
    (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [dLaLoweredG1Cc_unitModel_apply (I := I) (M := M) g₀ T g₁ g_bg htie x
    (fun i => m ((Equiv.swap (0 : Fin 4) 1) i))]
  rw [dLaLoweredG1Cc_unitModel_apply (I := I) (M := M) g₀ T g₁ g_bg htie x m]
  rw [show (Equiv.swap (0 : Fin 4) 1) 0 = 1 from Equiv.swap_apply_left 0 1,
    show (Equiv.swap (0 : Fin 4) 1) 1 = 0 from Equiv.swap_apply_right 0 1,
    show (Equiv.swap (0 : Fin 4) 1) 2 = 2 from by decide,
    show (Equiv.swap (0 : Fin 4) 1) 3 = 3 from by decide]

private lemma iCG_succ_cometricDT_zero_dla (g₀ : SmoothRiemannianMetric I M) (s m : ℕ) :
    iteratedCovGrad (I := I) g₀ (s + 2) s (m + 1)
      (cometricDoubleTraceField (I := I) g₀ s) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ s
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

private theorem exists_rfns_pureDT_tgrid (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + j) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) s j
              (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ s)).toSection x) ≤
          C j * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (j + 1) := by
  classical
  obtain ⟨S, hS_nn, hS⟩ := exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid_dla
    (I := I) (M := M) g₀ hδ₀
  obtain ⟨c0, hc0_nn, hc0⟩ := exists_fixedField_rfns_jet_dla (I := I) (M := M) g₀ (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun j => diagonalGridGrowthFactor (E := E) j *
      (c0 0 * ∑ l ∈ Finset.range (j + 1), fr ^ (s + 1) * S l),
    fun j => mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (mul_nonneg (hc0_nn 0) (Finset.sum_nonneg fun l _ =>
        mul_nonneg (by positivity) (hS_nn l))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hsFlat : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
      (fr ^ (s + 1) * S l) * Combinatorics.antidiagonalTupleGrid b l := by
    intro l
    refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁) l x) ?_
    rw [← hfr_def]
    have hins : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 1 l
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        S l * Combinatorics.antidiagonalTupleGrid b l := by
      rw [← sharpFlatEndoCc_eq_slotInsert_fullRaised_dla (I := I) (M := M) g₀ g₁]
      exact hS g₁ T htie hδ_le hδ0 hbound l x
    calc fr ^ (s + 1) * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)
        ≤ fr ^ (s + 1) * (S l * Combinatorics.antidiagonalTupleGrid b l) :=
          mul_le_mul_of_nonneg_left hins (by positivity)
      _ = (fr ^ (s + 1) * S l) * Combinatorics.antidiagonalTupleGrid b l := by ring
  rw [pureDTdla_eq_trace_fullRaised (I := I) (M := M) g₀ g₁ s]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ j (s + 2) (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
      (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) x) ?_
  have hzero : ∀ i' ∈ Finset.range (j + 1), i' ≠ 0 →
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) = 0 := by
    intro i' _ hi'0
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi'0
    rw [iCG_succ_cometricDT_zero_dla (I := I) (M := M) g₀ s m]
    rw [show ((0 : SmoothCcTensor g₀ (s + 2) (s + (m + 1))).toSection x) =
        (0 : TensorRSSpace (s + 2) (s + (m + 1)) I x) from by
      rw [SmoothCcTensor.toSection_zero]; rfl]
    rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ (s + 2) (s + (m + 1)) x]
    rw [zero_mul]
  have hsum_eq : (∑ i' ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + i') x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s i'
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)) =
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 0) x
          ((iteratedCovGrad (I := I) g₀ (s + 2) s 0
            (cometricDoubleTraceField (I := I) g₀ s)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - 0),
          riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
            ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
                (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) := by
    refine Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega)) ?_
    intro i' hi' hi'0
    exact hzero i' hi' hi'0
  rw [hsum_eq]
  have hc0' : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 0) x
      ((iteratedCovGrad (I := I) g₀ (s + 2) s 0
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x) ≤ c0 0 := hc0 0 x
  have hsumS : (∑ l ∈ Finset.range (j + 1 - 0),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x)) ≤
      (∑ l ∈ Finset.range (j + 1), fr ^ (s + 1) * S l) *
        antidiagonalTupleGridPartialSum b (j + 1) := by
    rw [show j + 1 - 0 = j + 1 from rfl]
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    refine le_trans (hsFlat l) ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) (hS_nn l))
    exact grid_le_dLaGridWin b hb (by omega)
  have hrfns_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) (s + 0) x
      ((iteratedCovGrad (I := I) g₀ (s + 2) s 0
        (cometricDoubleTraceField (I := I) g₀ s)).toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) (s + 0) x _
  have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - 0),
      riemannianFiberNormSq (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x
        ((iteratedCovGrad (I := I) g₀ (s + 2) (s + 2) l
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) :=
    Finset.sum_nonneg fun l _ =>
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (s + 2) ((s + 2) + l) x _
  refine le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hc0' hsumS hsum_nn (hc0_nn 0)) (appCcGdiag_nonneg (E := E) j)) ?_
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc (diagonalGridGrowthFactor (E := E) j) (c0 0)]

private theorem exists_rfns_pairTraceOpDla_tgrid (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 6 2 j
              (pairTraceOpDla (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C j * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (j + 1) := by
  classical
  obtain ⟨C2, hC2_nn, hC2⟩ := exists_rfns_pureDT_tgrid (I := I) (M := M) g₀ 2 hδ₀
  obtain ⟨C4, hC4_nn, hC4⟩ := exists_rfns_pureDT_tgrid (I := I) (M := M) g₀ 4 hδ₀
  refine ⟨fun j => diagonalGridGrowthFactor (E := E) j * ∑ i' ∈ Finset.range (j + 1),
      C2 i' * ∑ l ∈ Finset.range (j + 1 - i'), C4 l * antidiagonalTuplePairCount (i' + 1) (l + 1),
    fun j => mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hC2_nn i')
        (Finset.sum_nonneg fun l _ => mul_nonneg (hC4_nn l) (dLaPairCount_nonneg _ _))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := antidiagonalTupleGridPartialSum b (j + 1) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (j + 1)
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ j 6 4 2
    (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 2)
    (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 4) x) ?_
  have hcell : ∀ i' ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 2 i'
            (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 2)).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 6 4 l
              (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 4)).toSection x) ≤
      (C2 i' * ∑ l ∈ Finset.range (j + 1 - i'), C4 l * antidiagonalTuplePairCount (i' + 1) (l + 1)) * W := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 4 2 i'
          (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 2)).toSection x) ≤
        C2 i' * antidiagonalTupleGridPartialSum b (i' + 1) :=
      hC2 g₁ T htie hδ_le hδ0 hbound i' x
    have hA2 : (∑ l ∈ Finset.range (j + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 6 4 l
            (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 4)).toSection x)) ≤
        ∑ l ∈ Finset.range (j + 1 - i'), C4 l * antidiagonalTupleGridPartialSum b (l + 1) :=
      Finset.sum_le_sum fun l _ => hC4 g₁ T htie hδ_le hδ0 hbound l x
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 6 4 l
            (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 4)).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (4 + l) x _
    have hA1_rhs_nn : 0 ≤ C2 i' * antidiagonalTupleGridPartialSum b (i' + 1) :=
      mul_nonneg (hC2_nn i') (dLaGridWin_nonneg b hb (i' + 1))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show (C2 i' * ∑ l ∈ Finset.range (j + 1 - i'),
        C4 l * antidiagonalTuplePairCount (i' + 1) (l + 1)) * W =
        ∑ l ∈ Finset.range (j + 1 - i'),
          (C2 i' * (C4 l * antidiagonalTuplePairCount (i' + 1) (l + 1))) * W from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : antidiagonalTupleGridPartialSum b (i' + 1) * antidiagonalTupleGridPartialSum b (l + 1) ≤
        antidiagonalTuplePairCount (i' + 1) (l + 1) * antidiagonalTupleGridPartialSum b (j + 1) :=
      dLaGridWin_mul_le b hb (i' + 1) (l + 1) (j + 1) (by omega)
    calc C2 i' * antidiagonalTupleGridPartialSum b (i' + 1) * (C4 l * antidiagonalTupleGridPartialSum b (l + 1))
        = (C2 i' * C4 l) * (antidiagonalTupleGridPartialSum b (i' + 1) * antidiagonalTupleGridPartialSum b (l + 1)) := by ring
      _ ≤ (C2 i' * C4 l) * (antidiagonalTuplePairCount (i' + 1) (l + 1) * antidiagonalTupleGridPartialSum b (j + 1)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (hC2_nn i') (hC4_nn l)
      _ = (C2 i' * (C4 l * antidiagonalTuplePairCount (i' + 1) (l + 1))) * W := by
          rw [hW_def]
          ring
  calc diagonalGridGrowthFactor (E := E) j *
        ∑ i' ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
              ((iteratedCovGrad (I := I) g₀ 4 2 i'
                (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 2)).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 6 4 l
                  (cometricDoubleTraceSmoothCcTensor (I := I) (M := M) g₀ g₁ 4)).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) j *
          ∑ i' ∈ Finset.range (j + 1),
            (C2 i' * ∑ l ∈ Finset.range (j + 1 - i'),
              C4 l * antidiagonalTuplePairCount (i' + 1) (l + 1)) * W :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) j)
    _ = _ := by
        rw [← Finset.sum_mul, ← mul_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
private theorem deTurckLieDLaCoeffField_eq_pairTrace
    (g₀ g_bg g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg =
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (((-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x)) D) =
      (-1 : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x)) D) := by
    rw [show ((((-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (pairTraceOpDla (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x)) =
        (-1 : ℝ) • ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (pairTraceOpDla (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rfl
  rw [hsmul]
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [pairTraceOpDla_apply_toModel (I := I) (M := M) g₀ g₁
    (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffCovDerivBiContrFib (I := I) g₁ g_bg x) D from rfl]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      connDiffCovDerivBiContrFib (I := I) g₁ g_bg x) =
      connDiffCovDerivBiContrFibFixedFrame (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [dLaBiContrFibFixedFrame_toModel (I := I) g₁ g_bg (smoothOrthoFrame (I := I) g₁ x) x D v]
  have hXval : ∀ a b : Fin (Module.finrank ℝ E),
      unitModel (I := I) (M := M) g₀ 4 (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) x
        ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
          (smoothOrthoFrame (I := I) g₁ x b x : E)] =
      g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (v 0)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 1) +
        g₁.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (v 1)
          (smoothOrthoFrame (I := I) g₁ x a x) (smoothOrthoFrame (I := I) g₁ x b x)) (v 0) := by
    intro a b
    rw [dLaSymCc_unitModel_apply (I := I) (M := M) g₀ T g₁ g_bg htie x
      (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x)]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 0 = v 0 from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 1 = v 1 from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 2 =
      smoothOrthoFrame (I := I) g₁ x a x from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
        (smoothOrthoFrame (I := I) g₁ x b x : E)] : Fin 4 → TangentSpace I x) 3 =
      smoothOrthoFrame (I := I) g₁ x b x from rfl]
  rw [show (∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
      Tensor0SSpace.toModel D
          ![(smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)] *
        unitModel (I := I) (M := M) g₀ 4 (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) x
          ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
            (smoothOrthoFrame (I := I) g₁ x b x : E)]) =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] *
          unitModel (I := I) (M := M) g₀ 4 (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) x
            ![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x a x : E),
              (smoothOrthoFrame (I := I) g₁ x b x : E)] from Finset.sum_comm]
  rw [neg_one_mul, neg_one_mul]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hXval a b]
  ring

theorem rfns_iteratedCovGrad_deTurckLieDLaCoeffField_diagonalProductGrid_le
    (g₀ g_bg : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CPT, hCPT_nn, hCPT⟩ := exists_rfns_pairTraceOpDla_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨CX, hCX_nn, hCX⟩ := exists_rfns_dLaSym_tgrid (I := I) (M := M) g₀ g_bg hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i * ∑ i' ∈ Finset.range (i + 1),
      CPT i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * CX l)) * antidiagonalTuplePairCount (i' + 1) (l + 3),
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (hCPT_nn i')
        (Finset.sum_nonneg fun l _ => mul_nonneg
          (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCX_nn l))) (dLaPairCount_nonneg _ _))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := antidiagonalTupleGridPartialSum b (i + 3) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (i + 3)
  have hXtower : ∀ l, l ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      CX l * antidiagonalTupleGridPartialSum b (l + 3) := by
    intro l _
    exact hCX g₁ T htie hδ_le hδ0 hbound l x
  have hWtower : ∀ l, l ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) ≤
      (fr * (fr * CX l)) * antidiagonalTupleGridPartialSum b (l + 3) := by
    intro l hl
    have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 6 sigmaE0dla
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))
        (fun y d => by
          rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) l x
    rw [hperm]
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 5 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 1
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1
          (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)) l x
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 5 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 1
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) ≤
        fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg) l x
    have h3 := hXtower l hl
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x)
        ≤ fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 5 l
              (slotExtendIter (I := I) (M := M) g₀ 0 4 1
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) := h1
      _ ≤ fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x)) :=
          mul_le_mul_of_nonneg_left h2 hfr_nn
      _ ≤ fr * (fr * (CX l * antidiagonalTupleGridPartialSum b (l + 3))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hfr_nn) hfr_nn
      _ = (fr * (fr * CX l)) * antidiagonalTupleGridPartialSum b (l + 3) := by ring
  have hlift : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) := by
    rw [deTurckLieDLaCoeffField_eq_pairTrace (I := I) (M := M) g₀ g_bg g₁ T htie]
    rw [iteratedCovGrad_smul_dla]
    rw [show (((-1 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) =
        (-1 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceOpDla (I := I) (M := M) g₀ g₁)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [rfns_smul_dla (I := I) (M := M) g₀ 2 (2 + i) x]
    ring
  rw [hlift]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ i 2 6 2
    (pairTraceOpDla (I := I) (M := M) g₀ g₁)
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg))) x) ?_
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 6 2 i'
            (pairTraceOpDla (I := I) (M := M) g₀ g₁)).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) ≤
      (CPT i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * CX l)) * antidiagonalTuplePairCount (i' + 1) (l + 3)) * W := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 6 2 i'
          (pairTraceOpDla (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CPT i' * antidiagonalTupleGridPartialSum b (i' + 1) :=
      hCPT g₁ T htie hδ_le hδ0 hbound i' x
    have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - i'), (fr * (fr * CX l)) * antidiagonalTupleGridPartialSum b (l + 3) := by
      refine Finset.sum_le_sum fun l hl => ?_
      rw [Finset.mem_range] at hl
      exact hWtower l (by omega)
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
          ((iteratedCovGrad (I := I) g₀ 2 6 l
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0dla
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (dLaSymCc (I := I) (M := M) g₀ T g₁ g_bg)))).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _
    have hA1_rhs_nn : 0 ≤ CPT i' * antidiagonalTupleGridPartialSum b (i' + 1) :=
      mul_nonneg (hCPT_nn i') (dLaGridWin_nonneg b hb (i' + 1))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show (CPT i' * ∑ l ∈ Finset.range (i + 1 - i'),
        (fr * (fr * CX l)) * antidiagonalTuplePairCount (i' + 1) (l + 3)) * W =
        ∑ l ∈ Finset.range (i + 1 - i'),
          (CPT i' * ((fr * (fr * CX l)) * antidiagonalTuplePairCount (i' + 1) (l + 3))) * W from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : antidiagonalTupleGridPartialSum b (i' + 1) * antidiagonalTupleGridPartialSum b (l + 3) ≤
        antidiagonalTuplePairCount (i' + 1) (l + 3) * antidiagonalTupleGridPartialSum b (i + 3) :=
      dLaGridWin_mul_le b hb (i' + 1) (l + 3) (i + 3) (by omega)
    calc CPT i' * antidiagonalTupleGridPartialSum b (i' + 1) * ((fr * (fr * CX l)) * antidiagonalTupleGridPartialSum b (l + 3))
        = (CPT i' * (fr * (fr * CX l))) *
            (antidiagonalTupleGridPartialSum b (i' + 1) * antidiagonalTupleGridPartialSum b (l + 3)) := by ring
      _ ≤ (CPT i' * (fr * (fr * CX l))) *
            (antidiagonalTuplePairCount (i' + 1) (l + 3) * antidiagonalTupleGridPartialSum b (i + 3)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (hCPT_nn i')
            (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCX_nn l)))
      _ = (CPT i' * ((fr * (fr * CX l)) * antidiagonalTuplePairCount (i' + 1) (l + 3))) * W := by
          rw [hW_def]
          ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]
  beta_reduce
  rw [hW_def]
  rfl

open DifferentialGeometry.PDE.DeTurck.RicciLinearization (Icc_subset_realizedSmallSet) in
theorem deTurckLieDLaCoeffField_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieConnDiffDerivCoeffField (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤ P i := by
  classical
  set δ₁ : ℝ := max δ₀ 0 with hδ₁_def
  have hδ₁_nn : 0 ≤ δ₁ := le_max_right _ _
  have hδ₁_lt : δ₁ < 1 := max_lt hδ₀ one_pos
  obtain ⟨C, hC_nn, hC⟩ :=
    rfns_iteratedCovGrad_deTurckLieDLaCoeffField_diagonalProductGrid_le
      (I := I) (M := M) g₀ g_bg hδ₁_lt
  obtain ⟨K, hK_nn, hK⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3),
      K k * (1 + ((a + 3 : ℕ) : ℝ) * R ^ 2),
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (hK_nn k) (by positivity)), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set g₁ : SmoothRiemannianMetric I M := realizedFam (I := I) g₀ T T' hδ hδ' s with hg₁_def
  set Pc : SmoothCcTensor g₀ 0 2 := convexPerturbation (I := I) g₀ T T' s with hPc_def
  have hδs_raw : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc)
      (|1 - s| * δ' + |s| * δ) := by
    rw [hPc_def]
    exact convexPerturbation_gFibreOpBound_abs (I := I) g₀ T T' hδ hδ' s
  set δP : ℝ := max (|1 - s| * δ' + |s| * δ) 0 with hδP_def
  have hδP_nn : 0 ≤ δP := le_max_right _ _
  have hδP_bound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ Pc) δP :=
    gFibreOpBound_mono_of_le (I := I) (M := M) g₀ _ (le_max_left _ _) hδs_raw
  have hδP_le : δP ≤ δ₁ := by
    refine max_le ?_ hδ₁_nn
    rw [abs_of_nonneg h1ms, abs_of_nonneg hs0]
    have h1 : δ' ≤ δ₁ := le_trans hδ'_le (le_max_left _ _)
    have h2 : δ ≤ δ₁ := le_trans hδ_le (le_max_left _ _)
    nlinarith [h1, h2]
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ Pc y v w := by
    intro y v w
    rw [hg₁_def, hPc_def]
    exact realizedFam_inner_of_mem (I := I) g₀ T T' hδ hδ'
      (Icc_subset_realizedSmallSet hδ_lt hδ'_lt hs) y v w
  have hPball : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ≤ R := by
    intro j hj
    have heq : iteratedCovGrad (I := I) g₀ 0 2 j Pc
        = (1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
          + s • iteratedCovGrad (I := I) g₀ 0 2 j T := by
      rw [hPc_def]
      rw [show convexPerturbation (I := I) g₀ T T' s = (1 - s) • T' + s • T from rfl,
        iteratedCovGrad_add, iteratedCovGrad_smul_dla, iteratedCovGrad_smul_dla]
    rw [heq]
    calc ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'
            + s • iteratedCovGrad (I := I) g₀ 0 2 j T‖
        ≤ ‖(1 - s) • iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + ‖s • iteratedCovGrad (I := I) g₀ 0 2 j T‖ := norm_add_le _ _
      _ = (1 - s) * ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖
            + s * ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg h1ms, abs_of_nonneg hs0]
      _ ≤ (1 - s) * R + s * R :=
          add_le_add (mul_le_mul_of_nonneg_left (hT'ball j hj) h1ms)
            (mul_le_mul_of_nonneg_left (hTball j hj) hs0)
      _ = R := by ring
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x) :=
    fun x => hC g₁ Pc htie hδP_le hδP_nn hδP_bound i x
  have hint_k : ∀ k ∈ Finset.range (i + 3), MeasureTheory.Integrable
      (fun x => ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun k _ => (hK Pc hPball k).1
  have hint : MeasureTheory.Integrable
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (MeasureTheory.integrable_finset_sum (Finset.range (i + 3)) hint_k).const_mul (C i)
  have hnorm := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (deTurckLieConnDiffDerivCoeffField (I := I) (M := M) g₀ g₁ g_bg))
    (fun x => C i * ∑ k ∈ Finset.range (i + 3),
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) Pc).toSection x))
    hint hpt
  refine le_trans hnorm ?_
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_finset_sum (Finset.range (i + 3)) hint_k]
  refine mul_le_mul_of_nonneg_left ?_ (hC_nn i)
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  refine le_trans (hK Pc hPball k).2 ?_
  refine mul_le_mul_of_nonneg_left ?_ (hK_nn k)
  have hsum_le : (∑ j ∈ Finset.range (k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ^ 2) ≤ ((a + 3 : ℕ) : ℝ) * R ^ 2 := by
    calc (∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j Pc‖ ^ 2)
        ≤ ∑ j ∈ Finset.range (k + 1), R ^ 2 := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_range] at hj
          have hjle : j ≤ a + 2 := by omega
          have h := hPball j hjle
          nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j Pc), h, hR]
      _ = ((k + 1 : ℕ) : ℝ) * R ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ((a + 3 : ℕ) : ℝ) * R ^ 2 := by
          have hcast : ((k + 1 : ℕ) : ℝ) ≤ ((a + 3 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : k + 1 ≤ a + 3)
          nlinarith [sq_nonneg R]
  linarith [hsum_le]

end DLaGridBrick

end DifferentialGeometry.Integral.Connection

end
