import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerCurvDiffGridWindow
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerRiemannLoweredDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerRiemannMixedBiContraction
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulParallelRaiseJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Tuple.NatAntidiagonal


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (metricCauchySchwarzBound ccTensorBilinSymm smoothCcTensorBilinForm ccTensorBilin_apply ccTensorModel ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma appCcRS_zero_left_cc (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (W : SmoothCcTensor g₀ a b) :
    ccOperatorFieldComp (I := I) (M := M) g₀ a b c (0 : SmoothCcTensor g₀ b c) W = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ a b c (0 : SmoothCcTensor g₀ b c) W).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from
        (0 : SmoothCcTensor g₀ b c).toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((0 : SmoothCcTensor g₀ b c).toSection x) = (0 : TensorRSSpace b c I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rw [show ((0 : SmoothCcTensor g₀ a c).toSection x) = (0 : TensorRSSpace a c I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma appCcRS_right_zero_cc (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) :
    ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ (0 : SmoothCcTensor g₀ a b) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ (0 : SmoothCcTensor g₀ a b)).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
          (0 : SmoothCcTensor g₀ a b).toSection x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((0 : SmoothCcTensor g₀ a b).toSection x) = (0 : TensorRSSpace a b I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rw [show ((0 : SmoothCcTensor g₀ a c).toSection x) = (0 : TensorRSSpace a c I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rw [show ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
      (0 : TensorRSSpace a b I x)) D) = 0 from rfl]
  rw [map_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covGrad_slotExtend_toSection_rsDomDomCongr_b
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Φ : SmoothCcTensor g r s) (x : M) :
    (covGrad (I := I) (M := M) g (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g r s Φ)).toSection x =
      tensorRS_domDomCongr (I := I) (M := M) (r := r + 1) (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        ((slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) := by
  classical
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hfib : ∀ (y : Tensor0SSpace (s + 1 + 1) I x) (w : Fin (s + 1 + 1) → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace (s + 1 + 1) I x) w := fun _ _ => rfl
  conv_rhs => rw [hfib, rsDomDomCongr_apply_eval (I := I) (M := M) (r := r + 1)
    (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
    ((slotExtend (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ)).toSection x) d m]
  conv_rhs => rw [← hfib]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g (r + 1) (s + 1)
    (slotExtend (I := I) (M := M) g r s Φ) x d m]
  rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.tensorCovDerivAt_slotExtend_eq
    (I := I) (M := M) g r s Φ x (m 0)]
  rw [show Matrix.vecTail m =
      Fin.cons (m 1) (fun k : Fin s => m (Fin.succ (Fin.succ k))) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · change m (Fin.succ 0) = _
      rw [Fin.cons_zero]; rfl
    · change m (Fin.succ (Fin.succ i)) = _
      rw [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g r s x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      tensorCovDerivAt (I := I) (M := M) g r s Φ x (m 0))
    d (m 1) (fun k : Fin s => m (Fin.succ (Fin.succ k)))]
  rw [slotExtend_toSection (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) x]
  rw [show (fun k => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) k)) =
      Fin.cons (m 1) (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))
      from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [Fin.cons_zero]
      rw [Equiv.swap_apply_left]
    · rw [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g r (s + 1) x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g r s Φ).toSection x)
    d (m 1) (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g r s Φ x
    ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) d (m 1))
    (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))]
  have hdir : m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (0 : Fin (s + 1)))) = m 0 := by
    rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl, Equiv.swap_apply_right]
  have htail : (Matrix.vecTail (fun k : Fin (s + 1) =>
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))) =
      (fun k : Fin s => m (Fin.succ (Fin.succ k))) := by
    funext k
    change m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (Fin.succ k))) =
      m (Fin.succ (Fin.succ k))
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact (Fin.succ_ne_zero _)
    · rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
      exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  rw [hdir, htail]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotExtend_zero_cc (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    slotExtend (I := I) (M := M) g r s (0 : SmoothCcTensor g r s) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [show ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (slotExtend (I := I) (M := M) g r s (0 : SmoothCcTensor g r s)).toSection x) D) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (0 : SmoothCcTensor g r s).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((0 : SmoothCcTensor g r s).toSection x) = (0 : TensorRSSpace r s I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      (0 : TensorRSSpace r s I x)).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) =
      (0 : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D) from rfl]
  rw [ContinuousLinearMap.zero_comp, map_zero]
  rw [show ((0 : SmoothCcTensor g (r + 1) (s + 1)).toSection x) =
      (0 : TensorRSSpace (r + 1) (s + 1) I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma rsDomDomCongrSection_zero_cc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) :
    rsDomDomCongrSection (I := I) (M := M) g r s σ (0 : SmoothCcTensor g r s) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have h0 : ((0 : SmoothCcTensor g r s).toSection x) = (0 : TensorRSSpace r s I x) := by
    rw [SmoothCcTensor.toSection_zero]; rfl
  rw [rsDomDomCongrSection_toSection, h0]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hfib : ∀ (y : Tensor0SSpace s I x) (w : Fin s → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace s I x) w := fun _ _ => rfl
  rw [hfib, hfib]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (0 : TensorRSSpace r s I x) D m]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covGrad_slotExtend_parallel (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s)
    (hΦ : covGrad (I := I) (M := M) g r s Φ = 0) :
    covGrad (I := I) (M := M) g (r + 1) (s + 1)
      (slotExtend (I := I) (M := M) g r s Φ) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [covGrad_slotExtend_toSection_rsDomDomCongr_b (I := I) (M := M) g r s Φ x]
  rw [hΦ]
  rw [slotExtend_zero_cc (I := I) (M := M) g r (s + 1)]
  rw [show ((0 : SmoothCcTensor g (r + 1) (s + 1 + 1)).toSection x) =
      (0 : TensorRSSpace (r + 1) (s + 1 + 1) I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hfib : ∀ (y : Tensor0SSpace (s + 1 + 1) I x) (w : Fin (s + 1 + 1) → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace (s + 1 + 1) I x) w := fun _ _ => rfl
  rw [hfib, hfib]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
    (0 : TensorRSSpace (r + 1) (s + 1 + 1) I x) D m]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma slotExtendIter_parallel (g₀ : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c)
    (hΦ : covGrad (I := I) (M := M) g₀ b c Φ = 0) :
    ∀ j : ℕ, covGrad (I := I) (M := M) g₀ (b + j) (c + j)
      (slotExtendIter (I := I) (M := M) g₀ b c j Φ) = 0
  | 0 => hΦ
  | (j + 1) => by
      rw [show slotExtendIter (I := I) (M := M) g₀ b c (j + 1) Φ =
          slotExtend (I := I) (M := M) g₀ (b + j) (c + j)
            (slotExtendIter (I := I) (M := M) g₀ b c j Φ) from rfl]
      exact covGrad_slotExtend_parallel (I := I) (M := M) g₀ (b + j) (c + j)
        (slotExtendIter (I := I) (M := M) g₀ b c j Φ)
        (slotExtendIter_parallel g₀ b c Φ hΦ j)

omit [NeZero (Module.finrank ℝ E)] in
lemma iteratedCovGrad_appCcRS_parallel (g₀ : SmoothRiemannianMetric I M)
    (a b c : ℕ) (Φ : SmoothCcTensor g₀ b c)
    (hΦ : covGrad (I := I) (M := M) g₀ b c Φ = 0) (W : SmoothCcTensor g₀ a b) :
    ∀ j : ℕ, iteratedCovGrad (I := I) g₀ a c j (ccOperatorFieldComp (I := I) (M := M) g₀ a b c Φ W) =
      ccOperatorFieldComp (I := I) (M := M) g₀ a (b + j) (c + j)
        (slotExtendIter (I := I) (M := M) g₀ b c j Φ)
        (iteratedCovGrad (I := I) g₀ a b j W)
  | 0 => by
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      rfl
  | (j + 1) => by
      rw [iteratedCovGrad_succ]
      rw [iteratedCovGrad_appCcRS_parallel g₀ a b c Φ hΦ W j]
      rw [covGrad_appCcRS_eq (I := I) (M := M) g₀ a (b + j) (c + j)
        (slotExtendIter (I := I) (M := M) g₀ b c j Φ)
        (iteratedCovGrad (I := I) g₀ a b j W)]
      rw [slotExtendIter_parallel (I := I) (M := M) g₀ b c Φ hΦ j]
      rw [appCcRS_zero_left_cc (I := I) (M := M) g₀ a (b + j) ((c + j) + 1)
        (iteratedCovGrad (I := I) g₀ a b j W)]
      rw [zero_add]
      rw [show covGrad (I := I) (M := M) g₀ a (b + j) (iteratedCovGrad (I := I) g₀ a b j W) =
          iteratedCovGrad (I := I) g₀ a b (j + 1) W from
        (iteratedCovGrad_succ (I := I) g₀ a b j W).symm]
      rfl

def pairTraceKernel (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 6 2 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 6 4 2
    (cometricDoubleTraceField (I := I) g₀ 2) (cometricDoubleTraceField (I := I) g₀ 4)

lemma phiDtPair_covGrad_zero (g₀ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 6 2 (pairTraceKernel (I := I) (M := M) g₀) = 0 := by
  rw [pairTraceKernel]
  rw [covGrad_appCcRS_eq (I := I) (M := M) g₀ 6 4 2
    (cometricDoubleTraceField (I := I) g₀ 2) (cometricDoubleTraceField (I := I) g₀ 4)]
  rw [cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2]
  rw [cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 4]
  rw [appCcRS_zero_left_cc (I := I) (M := M) g₀ 6 4 3
    (cometricDoubleTraceField (I := I) g₀ 4)]
  rw [appCcRS_right_zero_cc (I := I) (M := M) g₀ 6 5 3
    (slotExtend (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2))]
  rw [add_zero]

def pairTraceKernelSlotPerm : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![1, 3, 4, 5, 0, 2] : Fin 6 → Fin 6) i,
   fun i => (![4, 0, 5, 1, 2, 3] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0S_zero_rank_decomp (x : M) (t : Tensor0SSpace 0 I x) :
    t = (Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0)) • unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [show m = (fun i : Fin 0 => i.elim0 : Fin 0 → E) from by
    funext k
    exact k.elim0]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x)
      (fun i : Fin 0 => i.elim0) = 1 from by
    rw [unitTensor, Tensor0SSpace.toModel_ofModel]
    rfl]
  rw [smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma slotExtendIter_two_toModel (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (x : M) (D : Tensor0SSpace 2 I x)
    (u : Fin 6 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1] *
        unitModel (I := I) (M := M) g₀ 4 X x (fun k : Fin 4 => u (Fin.natAdd 2 k)) := by
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D)) from rfl]
  have hkey1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 5)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D)))
    (v0 := u 0) (vs := Matrix.vecTail u)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey1
  rw [show (Fin.cons (u 0) (Matrix.vecTail u) : Fin 6 → TangentSpace I x) = u from by
    funext k
    refine Fin.cases rfl (fun i => rfl) k] at hkey1
  rw [← hkey1]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D) (u 0)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 4 x).symm
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)))) from rfl]
  rw [show (Matrix.vecTail u : Fin 5 → TangentSpace I x) =
      Fin.cons (u 1) (fun k : Fin 4 => u (Fin.natAdd 2 k)) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rfl
    · change u (Fin.succ (Fin.succ i)) = u (Fin.natAdd 2 i)
      congr 1
      exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)]
  have hkey2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 4)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 4 x).symm
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)))))
    (v0 := u 1) (vs := fun k : Fin 4 => u (Fin.natAdd 2 k))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey2
  rw [← hkey2]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0))) (u 1)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1)) from rfl]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (v0 := u 1)
      (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D) (v0 := u 0) (vs := Fin.cons (u 1) (fun i : Fin 0 => i.elim0))
    rw [h2]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => i2.elim0) i
  have hdecomp := tensor0S_zero_rank_decomp (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x)
      (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x)
        (unitTensor (I := I) (M := M) x) from rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 12800000 in
theorem mixedCoeff_backgroundDifference_eq_pairTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceKernel (I := I) (M := M) g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) D) v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x
            ![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] *
          Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) D) =
        (riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x D -
          riemannBiContrFib (I := I) g₀ x D) from by
      rw [show ((ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) =
        (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁).toSection x -
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rfl]
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
    rw [show riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x =
        riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁
          (smoothOrthoFrame (I := I) g₀ x) x from rfl]
    rw [show riemannBiContrFib (I := I) g₀ x =
        riemannBiContrFibFixedFrame (I := I) g₀ (smoothOrthoFrame (I := I) g₀ x) x from rfl]
    rw [riemannMixedBiContrFibFixedFrame_toModel (I := I) g₀ g₁
      (smoothOrthoFrame (I := I) g₀ x) x D v]
    rw [riemannBiContrFibFixedFrame_toModel (I := I) g₀ (smoothOrthoFrame (I := I) g₀ x) x D v]
    rw [← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [riemannLoweredBackgroundDifference_unitModel_apply (I := I) (M := M) g₀ g₁ x
      (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
        (smoothOrthoFrame (I := I) g₀ x b x : E)] : Fin 4 → TangentSpace I x)]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
        (smoothOrthoFrame (I := I) g₀ x b x : E)] : Fin 4 → TangentSpace I x) 0 = v 0 from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
        (smoothOrthoFrame (I := I) g₀ x b x : E)] : Fin 4 → TangentSpace I x) 1 = v 1 from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
        (smoothOrthoFrame (I := I) g₀ x b x : E)] : Fin 4 → TangentSpace I x) 2 =
      smoothOrthoFrame (I := I) g₀ x a x from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
        (smoothOrthoFrame (I := I) g₀ x b x : E)] : Fin 4 → TangentSpace I x) 3 =
      smoothOrthoFrame (I := I) g₀ x b x from rfl]
    ring
  rw [hLHS]
  set X : SmoothCcTensor g₀ 0 4 :=
    riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ with hX_def
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 1, w 3] *
          unitModel (I := I) (M := M) g₀ 4 X x ![w 4, w 5, w 0, w 2] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          tensorRS_domDomCongr pairTraceKernelSlotPerm
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) pairTraceKernelSlotPerm
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendIter_two_toModel (I := I) (M := M) g₀ X x D
      (fun i => w (pairTraceKernelSlotPerm i))]
    rfl
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceKernel (I := I) (M := M) g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) v =
      2 * ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] *
          unitModel (I := I) (M := M) g₀ 4 X x
            ![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] := by
    rw [show (((2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceKernel (I := I) (M := M) g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) =
        (2 : ℝ) • ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceKernel (I := I) (M := M) g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [show ((2 : ℝ) • ((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceKernel (I := I) (M := M) g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) :
        TensorRSSpace 2 2 I x) D =
        (2 : ℝ) • (((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceKernel (I := I) (M := M) g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) from rfl]
    rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    congr 1
    rw [show (((ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2 (pairTraceKernel (I := I) (M := M) g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 pairTraceKernelSlotPerm
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) =
        (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          cometricDoubleTraceFib (I := I) g₀ 2 x)
          ((show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 4 I x from
            cometricDoubleTraceFib (I := I) g₀ 4 x) Y) from by
      rw [hY_def]
      rw [appCcRS_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ 2 x]
    rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        ((show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 4 I x from
          cometricDoubleTraceFib (I := I) g₀ 4 x) Y))
      (fun j => (v j : E))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
    rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel Y)
      (Fin.cons ((smoothOrthoFrame (I := I) g₀ x b x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ x b x : TangentSpace I x) : E)
          (fun j => (v j : E))))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hYval]
    rfl
  rw [hRHS]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

end Connection
end Integral
end DifferentialGeometry
end
