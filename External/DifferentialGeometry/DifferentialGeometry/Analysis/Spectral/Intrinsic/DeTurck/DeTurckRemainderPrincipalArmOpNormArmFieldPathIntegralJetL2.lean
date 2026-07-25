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

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_jointContMDiffOn
    (g₀ : SmoothRiemannianMetric I M) (r sIdx i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + i) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (sIdx + i) I z) q.1
        ((iteratedCovGrad (I := I) g₀ r sIdx i (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S) := by
  induction i with
  | zero => exact hjoint
  | succ j ih =>
    exact covGrad_step_jointContMDiffOn (I := I) (M := M) g₀ r (sIdx + j)
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)) S ih

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem riemannianFiberNormSq_jointContinuousOn
    (g₀ : SmoothRiemannianMetric I M) (r sIdx : ℕ)
    (Ψ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ)
    (hSI : Set.Icc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r sIdx p.2 ((Ψ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
  have hIccprod : (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) ⊆
      (fun p : ℝ × M => (p.2, p.1)) ⁻¹' ((Set.univ : Set M) ×ˢ S) := by
    rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ⟨Set.mem_univ _, hSI ht⟩
  have hswapCont : Continuous (fun p : ℝ × M => (p.2, p.1)) := by fun_prop
  have hv : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) p.2 ((Ψ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
    refine (hjoint.continuousOn.comp hswapCont.continuousOn hIccprod).congr ?_
    rintro ⟨t, x⟩ -
    rfl
  have hψ : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk'
        (TensorRSModel r sIdx ℝ E →L[ℝ] TensorRSModel r sIdx ℝ E →L[ℝ] ℝ)
        (E := fun x : M => TensorRSSpace r sIdx I x →L[ℝ] TensorRSSpace r sIdx I x →L[ℝ] ℝ)
        p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    ((DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorRSRiemannianInnerCLM_continuous
      (I := I) (M := M) g₀ r sIdx).comp continuous_snd).continuousOn
  have happ : ContinuousOn
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2 ((Ψ p.1).toSection p.2) ((Ψ p.1).toSection p.2)))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    ContinuousOn.clm_bundle_apply₂ (F₁ := TensorRSModel r sIdx ℝ E)
      (F₂ := TensorRSModel r sIdx ℝ E) (F₃ := ℝ) (b := fun p : ℝ × M => p.2) hψ hv hv
  have hscalar : ContinuousOn
      (fun p : ℝ × M =>
        DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2 ((Ψ p.1).toSection p.2) ((Ψ p.1).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := by
    intro p hp
    have hp2 := ((FiberBundle.continuousWithinAt_totalSpace ℝ
      (fun p : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) p.2
        (DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g₀ r sIdx p.2
          ((Ψ p.1).toSection p.2) ((Ψ p.1).toSection p.2)))).mp (happ p hp)).2
    exact hp2
  refine hscalar.congr ?_
  rintro ⟨t, x⟩ -
  simp only
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ r sIdx x
      ((Ψ t).toSection x),
    DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem dscr_pathIntegralCoeffField_congr
    (g₀ : SmoothRiemannianMetric I M) (r sIdx : ℕ)
    (Ψ₁ Ψ₂ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hj₁ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ₁ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hj₂ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Ψ₂ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hΨ : Ψ₁ = Ψ₂) :
    pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Ψ₁ S hS hSI hj₁ =
      pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Ψ₂ S hS hSI hj₂ := by
  subst hΨ
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 3200000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
private theorem iteratedCovGrad_pathIntegralCoeffField_comm
    (g₀ : SmoothRiemannianMetric I M) (r sIdx i : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r sIdx) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r sIdx ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r sIdx ℝ E)
        (E := fun z : M => TensorRSSpace r sIdx I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (hji : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + i) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (sIdx + i) I z) q.1
        ((iteratedCovGrad (I := I) g₀ r sIdx i (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S)) :
    iteratedCovGrad (I := I) g₀ r sIdx i
        (pathIntegralCoeffField (I := I) (M := M) g₀ r sIdx Φ S hS hSI hjoint) =
      pathIntegralCoeffField (I := I) (M := M) g₀ r (sIdx + i)
        (fun t => iteratedCovGrad (I := I) g₀ r sIdx i (Φ t)) S hS hSI hji := by
  induction i with
  | zero =>
    rw [iteratedCovGrad_zero]
    exact dscr_pathIntegralCoeffField_congr (I := I) g₀ r sIdx Φ
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx 0 (Φ t)) S hS hSI hjoint hji
      (by funext t; rw [iteratedCovGrad_zero])
  | succ j ih =>
    have hjg_j : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + j) ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + j) ℝ E)
          (E := fun z : M => TensorRSSpace r (sIdx + j) I z) q.1
          ((iteratedCovGrad (I := I) g₀ r sIdx j (Φ q.2)).toSection q.1))
        ((Set.univ : Set M) ×ˢ S) :=
      iteratedCovGrad_jointContMDiffOn (I := I) g₀ r sIdx j Φ S hjoint
    have hjgsucc : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        (I.prod 𝓘(ℝ, TensorRSModel r (sIdx + j + 1) ℝ E)) ∞
        (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (sIdx + j + 1) ℝ E)
          (E := fun z : M => TensorRSSpace r (sIdx + j + 1) I z) q.1
          ((covGrad (I := I) (M := M) g₀ r (sIdx + j)
              (iteratedCovGrad (I := I) g₀ r sIdx j (Φ q.2))).toSection q.1))
        ((Set.univ : Set M) ×ˢ S) :=
      covGrad_step_jointContMDiffOn (I := I) (M := M) g₀ r (sIdx + j)
        (fun t => iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)) S hjg_j
    rw [iteratedCovGrad_succ, ih hjg_j]
    rw [covGrad_pathIntegral_comm (I := I) (M := M) g₀ r (sIdx + j)
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)) S hS hSI hjg_j hjgsucc]
    exact dscr_pathIntegralCoeffField_congr (I := I) g₀ r (sIdx + j + 1)
      (fun t => covGrad (I := I) (M := M) g₀ r (sIdx + j)
        (iteratedCovGrad (I := I) g₀ r sIdx j (Φ t)))
      (fun t => iteratedCovGrad (I := I) g₀ r sIdx (j + 1) (Φ t)) S hS hSI hjgsucc hji
      (by funext t; rw [iteratedCovGrad_succ])

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem armField_pathIntegral_jetL2_perOrder_le
    (g₀ : SmoothRiemannianMetric I M) (r : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r 2) {δ δ' : ℝ}
    (hSI : Set.uIcc (0 : ℝ) 1 ⊆ DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedSmallSet (δ := δ) (δ' := δ'))
    (hSopen : IsOpen (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedSmallSet (δ := δ) (δ' := δ')))
    (hjoint : linearizedRicciThreeArmHjoint (I := I) (M := M) g₀ r Φ (δ := δ) (δ' := δ'))
    (i : ℕ) {B : ℝ} (_hB : 0 ≤ B)
    (hΦjet : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ s)‖ ^ 2 ≤ B ^ 2) :
    ‖iteratedCovGrad (I := I) g₀ r 2 i
        (pathIntegralCoeffField (I := I) (M := M) g₀ r 2 Φ
          (DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedSmallSet (δ := δ) (δ' := δ')) hSopen hSI hjoint)‖ ^ 2 ≤ B ^ 2 := by
  classical
  set S : Set ℝ :=
    DifferentialGeometry.PDE.DeTurck.RicciLinearization.realizedSmallSet
      (δ := δ) (δ' := δ') with hS_def
  have hjointC : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r 2 ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r 2 ℝ E)
        (E := fun z : M => TensorRSSpace r 2 I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S) := hjoint
  have hji : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r (2 + i) ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r (2 + i) ℝ E)
        (E := fun z : M => TensorRSSpace r (2 + i) I z) q.1
        ((iteratedCovGrad (I := I) g₀ r 2 i (Φ q.2)).toSection q.1))
      ((Set.univ : Set M) ×ˢ S) :=
    iteratedCovGrad_jointContMDiffOn (I := I) g₀ r 2 i Φ S hjointC
  have hcomm : iteratedCovGrad (I := I) g₀ r 2 i
      (pathIntegralCoeffField (I := I) (M := M) g₀ r 2 Φ S hSopen hSI hjoint) =
      pathIntegralCoeffField (I := I) (M := M) g₀ r (2 + i)
        (fun t => iteratedCovGrad (I := I) g₀ r 2 i (Φ t)) S hSopen hSI hji :=
    iteratedCovGrad_pathIntegralCoeffField_comm (I := I) g₀ r 2 i Φ S hSopen hSI hjointC hji
  rw [hcomm]
  have hci : ∀ x : M, ContinuousOn (fun t : ℝ =>
      TensorRSSpace.toModel ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x))
      (Set.Icc (0 : ℝ) 1) := by
    intro x
    exact (DifferentialGeometry.PDE.DeTurck.RicciLinearization.jointContMDiff_toModel_continuous_slice
      (I := I) g₀ r (2 + i)
      (fun t => iteratedCovGrad (I := I) g₀ r 2 i (Φ t)) S hji x).mono
      (by rw [← Set.uIcc_of_le (zero_le_one (α := ℝ))]; exact hSI)
  have hri : ContinuousOn (fun p : ℝ × M =>
      riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) p.2
        ((iteratedCovGrad (I := I) g₀ r 2 i (Φ p.1)).toSection p.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) :=
    riemannianFiberNormSq_jointContinuousOn (I := I) g₀ r (2 + i)
      (fun t => iteratedCovGrad (I := I) g₀ r 2 i (Φ t)) S
      (by rw [← Set.uIcc_of_le (zero_le_one (α := ℝ))]; exact hSI) hji
  have hL2 := tensorL2NormSq_pathIntegralCoeffField_le_intervalIntegral_normSq
    (I := I) (M := M) g₀ r (2 + i)
    (fun t => iteratedCovGrad (I := I) g₀ r 2 i (Φ t)) S hSopen hSI hji hci hri
  refine le_trans hL2 ?_
  have hmono : (∫ t in (0 : ℝ)..1, ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ t)‖ ^ 2) ≤
      ∫ _t in (0 : ℝ)..1, B ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ intervalIntegrable_const ?_
    · have hFcont : ContinuousOn (fun p : ℝ × M =>
          riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) p.2
            ((iteratedCovGrad (I := I) g₀ r 2 i (Φ p.1)).toSection p.2))
          (Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set M)) := hri
      letI : MeasurableSpace E := borel E
      haveI : BorelSpace E := ⟨rfl⟩
      letI : MeasurableSpace M := borel M
      haveI : BorelSpace M := ⟨rfl⟩
      set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
      haveI : IsFiniteMeasure μ :=
        riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
      have hnormsq : ∀ t : ℝ,
          ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ t)‖ ^ 2 =
            ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) x
              ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x) ∂μ := by
        intro t
        rw [SmoothCcTensor.norm_def]
        have hsec : (fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
              (r := r) (s := 2 + i) (x := x)
              ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x)) =
            (iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toFun := by
          funext x
          rw [SmoothCcTensor.toFun_apply]
        rw [← hsec,
          tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i)
            (fun x => (iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x)]
      have hcontInt : ContinuousOn (fun t : ℝ =>
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) x
            ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x) ∂μ)
          (Set.Icc (0 : ℝ) 1) :=
        continuousOn_integral_of_compact_support (μ := μ) isCompact_univ hFcont
          (fun _ x _ hx => absurd (Set.mem_univ x) hx)
      have heq : (fun t : ℝ => ‖iteratedCovGrad (I := I) g₀ r 2 i (Φ t)‖ ^ 2) =
          fun t : ℝ => ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ r (2 + i) x
            ((iteratedCovGrad (I := I) g₀ r 2 i (Φ t)).toSection x) ∂μ := funext hnormsq
      rw [heq]
      exact hcontInt.intervalIntegrable_of_Icc (by norm_num)
    · exact fun t ht => hΦjet t ht
  refine le_trans hmono ?_
  rw [intervalIntegral.integral_const]
  simp

end

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
