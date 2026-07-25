import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.FiberNormRiemannianBridge
import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.RHSSmoothQuasilinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorExtension
import DifferentialGeometry.Geometry.Connection.TensorNabla.IteratedTensorCovDeriv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RicciDiffAffine
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieSummandLipschitz
















































noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor
open DifferentialGeometry.PDE.RicciFlow.HebeyBlock
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]






omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRHS_diff_frame_component_apply
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (deTurckRicciRHS (I := I) g_bg g₁ x - deTurckRicciRHS (I := I) g_bg g₂ x)
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) =
      deTurckRicciRHS (I := I) g_bg g₁ x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)
      - deTurckRicciRHS (I := I) g_bg g₂ x
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x) := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]






omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRHS_diff_frame_component_contMDiffOn
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        (deTurckRicciRHS (I := I) g_bg g₁ x - deTurckRicciRHS (I := I) g_bg g₂ x)
          (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source := by
  have h₁ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => deTurckRicciRHS (I := I) g_bg g₁ x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source :=
    combine_smoothness_of_summands (I := I) g_bg g₁ α i j
  have h₂ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => deTurckRicciRHS (I := I) g_bg g₂ x
        (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source :=
    combine_smoothness_of_summands (I := I) g_bg g₂ α i j
  refine (h₁.sub h₂).congr (fun x _ => ?_)
  exact deTurckRHS_diff_frame_component_apply (I := I) g_bg g₁ g₂ α x i j

set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in








omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem deTurckRHS_diff_gNorm_le_modelNorm_pointwise
    (g₀ : SmoothRiemannianMetric I M) (x₀ : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
    ∃ D : ℝ, 0 < D ∧ ∀ T : TensorRSSpace 0 2 I x₀,
      ‖T‖ ≤ D * ‖TensorRSSpace.toModel (𝕜 := ℝ) (I := I) T‖ :=
  gNorm_le_modelNorm_pointwise (I := I) (M := M) g₀ 0 2 x₀





def metricDiff02 (g₁ g₂ : SmoothRiemannianMetric I M) :
    Π b : M, TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ :=
  fun b => metricTensor02 (I := I) g₁ b - metricTensor02 (I := I) g₂ b

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem metricDiff02_apply
    (g₁ g₂ : SmoothRiemannianMetric I M) (b : M) (v w : TangentSpace I b) :
    metricDiff02 (I := I) g₁ g₂ b v w =
      g₁.inner b v w - g₂.inner b v w := by
  change (metricTensor02 (I := I) g₁ b - metricTensor02 (I := I) g₂ b) v w =
    g₁.inner b v w - g₂.inner b v w
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
  rfl






def metricDiff02Cov (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    TangentSpace I b →L[ℝ]
      (TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) :=
  (tensor02Cov (LeviCivita (I := I) g₀)).toFun
    (metricDiff02 (I := I) g₁ g₂) b





omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem metricDiff02Cov_eq_sub
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    metricDiff02Cov (I := I) g₀ g₁ g₂ b =
      (tensor02Cov (LeviCivita (I := I) g₀)).toFun
          (metricTensor02 (I := I) g₁) b
        - (tensor02Cov (LeviCivita (I := I) g₀)).toFun
          (metricTensor02 (I := I) g₂) b := by
  classical
  set cov := tensor02Cov (LeviCivita (I := I) g₀) with hcov_def
  have hcovOn := cov.isCovariantDerivativeOnUniv
  have hT₁ : MDiffAtTensor02 (metricTensor02 (I := I) g₁) b :=
    metricTensor02_mdiff (I := I) g₁ b
  have hT₂ : MDiffAtTensor02 (metricTensor02 (I := I) g₂) b :=
    metricTensor02_mdiff (I := I) g₂ b
  have hT₂neg : MDiffAtTensor02 (-(metricTensor02 (I := I) g₂)) b :=
    mdifferentiableAt_neg_section hT₂
  have hneg : cov.toFun (-(metricTensor02 (I := I) g₂)) b =
      - cov.toFun (metricTensor02 (I := I) g₂) b := by
    have hsum : cov.toFun (metricTensor02 (I := I) g₂
          + (-(metricTensor02 (I := I) g₂))) b =
        cov.toFun (metricTensor02 (I := I) g₂) b
          + cov.toFun (-(metricTensor02 (I := I) g₂)) b :=
      hcovOn.add hT₂ hT₂neg (Set.mem_univ b)
    rw [add_neg_cancel] at hsum
    have hzero : cov.toFun (0 : Π x : M,
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b = 0 :=
      hcovOn.zero (Set.mem_univ b)
    rw [hzero] at hsum
    exact eq_neg_of_add_eq_zero_right hsum.symm
  have hadd : cov.toFun (metricTensor02 (I := I) g₁
        + (-(metricTensor02 (I := I) g₂))) b =
      cov.toFun (metricTensor02 (I := I) g₁) b
        + cov.toFun (-(metricTensor02 (I := I) g₂)) b :=
    hcovOn.add hT₁ hT₂neg (Set.mem_univ b)
  have hdiff_eq : metricDiff02 (I := I) g₁ g₂ =
      metricTensor02 (I := I) g₁ + (-(metricTensor02 (I := I) g₂)) := by
    funext c
    simp only [metricDiff02, metricTensor02, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
  calc metricDiff02Cov (I := I) g₀ g₁ g₂ b
      = cov.toFun (metricDiff02 (I := I) g₁ g₂) b := rfl
    _ = cov.toFun (metricTensor02 (I := I) g₁
          + (-(metricTensor02 (I := I) g₂))) b := by rw [hdiff_eq]
    _ = cov.toFun (metricTensor02 (I := I) g₁) b
          + cov.toFun (-(metricTensor02 (I := I) g₂)) b := hadd
    _ = cov.toFun (metricTensor02 (I := I) g₁) b
          - cov.toFun (metricTensor02 (I := I) g₂) b := by rw [hneg]; abel

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in





omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricTensor02Cov_mdiffAtTensor03
    (g₀ g : SmoothRiemannianMetric I M) (x : M) :
    MDiffAtTensor03 (I := I)
      ((tensor02Cov (LeviCivita (I := I) g₀)).toFun (metricTensor02 (I := I) g)) x := by
  classical
  have hmetric : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) := g.contMDiff
  haveI hcov : CovariantDerivative.ContMDiffCovariantDerivative
      (tensor02Cov (LeviCivita (I := I) g₀)) ∞ :=
    tensor02Cov_isContMDiff (LeviCivita (I := I) g₀)
  have h_le : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) + 1 := by rw [ENat.coe_top_add_one]
  have hmetric₁ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((∞ : WithTop ℕ∞) + 1)
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) Set.univ :=
    contMDiffOn_univ.mpr (hmetric.of_le h_le)
  have hcovOn := hcov.contMDiff
  have hsmooth :=
    hcovOn.contMDiff (σ := metricTensor02 (I := I) g) hmetric₁
  exact (contMDiffOn_univ.mp hsmooth x).mdifferentiableAt (by simp)






def metricDiff02CovIterate (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    TangentSpace I b →L[ℝ]
      (TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) :=
  tensor02CovIterate (LeviCivita (I := I) g₀) (metricDiff02 (I := I) g₁ g₂) b

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in







omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricDiff02CovIterate_eq_sub
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (b : M) :
    metricDiff02CovIterate (I := I) g₀ g₁ g₂ b =
      tensor02CovIterate (LeviCivita (I := I) g₀) (metricTensor02 (I := I) g₁) b
        - tensor02CovIterate (LeviCivita (I := I) g₀) (metricTensor02 (I := I) g₂) b := by
  classical
  set cov := LeviCivita (I := I) g₀ with hcov_def
  have hinner_eq : (tensor02Cov cov).toFun (metricDiff02 (I := I) g₁ g₂) =
      (tensor02Cov cov).toFun (metricTensor02 (I := I) g₁)
        - (tensor02Cov cov).toFun (metricTensor02 (I := I) g₂) := by
    funext c
    have h := metricDiff02Cov_eq_sub (I := I) g₀ g₁ g₂ c
    have hlhs : metricDiff02Cov (I := I) g₀ g₁ g₂ c =
        (tensor02Cov cov).toFun (metricDiff02 (I := I) g₁ g₂) c := rfl
    rw [hlhs] at h
    rw [h]
    rfl
  have hS₁ : MDiffAtTensor03 (I := I)
      ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₁)) b :=
    metricTensor02Cov_mdiffAtTensor03 (I := I) g₀ g₁ b
  have hS₂ : MDiffAtTensor03 (I := I)
      ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₂)) b :=
    metricTensor02Cov_mdiffAtTensor03 (I := I) g₀ g₂ b
  calc metricDiff02CovIterate (I := I) g₀ g₁ g₂ b
      = (tensor03Cov cov).toFun
          ((tensor02Cov cov).toFun (metricDiff02 (I := I) g₁ g₂)) b := rfl
    _ = (tensor03Cov cov).toFun
          ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₁)
            - (tensor02Cov cov).toFun (metricTensor02 (I := I) g₂)) b := by
        rw [hinner_eq]
    _ = (tensor03Cov cov).toFun
          ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₁)) b
        - (tensor03Cov cov).toFun
          ((tensor02Cov cov).toFun (metricTensor02 (I := I) g₂)) b :=
        tensor03Cov_sub cov hS₁ hS₂
    _ = tensor02CovIterate cov (metricTensor02 (I := I) g₁) b
        - tensor02CovIterate cov (metricTensor02 (I := I) g₂) b := rfl




omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem tensor03_pairing_contMDiff
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b)))
    {Y Z W : Π x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Y b)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Z b)))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (W b))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => S b (Y b) (Z b) (W b)) := by
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b (Y b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      (b := fun b : M => b) (ϕ := fun b => S b) (v := fun b => Y b) hS hY
  have h2 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (S b (Y b) (Z b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (b := fun b : M => b) (ϕ := fun b => S b (Y b)) (v := fun b => Z b) h1 hZ
  have h3 : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => TotalSpace.mk' ℝ (E := fun _ : M => ℝ) b (S b (Y b) (Z b) (W b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun _ : M => ℝ)
      (b := fun b : M => b) (ϕ := fun b => S b (Y b) (Z b)) (v := fun b => W b) h2 hW
  intro x
  exact (contMDiffAt_section (F := ℝ) (E := fun _ : M => ℝ) x).mp (h3 x)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in





omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem tensor03Cov_quad_apply_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b)))
    (Y Z W U : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => ((((tensor03Cov cov).toFun S x (Y x)) (Z x)) (W x)) (U x)) := by
  have h_eq : ∀ x : M,
      ((((tensor03Cov cov).toFun S x (Y x)) (Z x)) (W x)) (U x) =
        extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x (Y x)
          - S x (cov.toFun Z x (Y x)) (W x) (U x)
          - S x (Z x) (cov.toFun W x (Y x)) (U x)
          - S x (Z x) (W x) (cov.toFun U x (Y x)) := by
    intro x
    have hSx : MDiffAtTensor03 S x := (hS x).mdifferentiableAt (by simp)
    have hYx := (Y.contMDiff x).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hZx := (Z.contMDiff x).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hWx := (W.contMDiff x).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hUx := (U.contMDiff x).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have h := tensor03CovAt_apply_of_diff_extend cov hSx hYx hZx hWx hUx
    rw [tensor03Cov_toFun, tensor03CovFun_apply, h]
    rfl
  have h_pair : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => S b (Z b) (W b) (U b)) :=
    tensor03_pairing_contMDiff hS Z.contMDiff W.contMDiff U.contMDiff
  have h_extDeriv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x)
        x (extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x)) :=
    cotangentCov_extDerivFun_smooth h_pair
  have h_extDeriv_Y : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x (Y x)) := by
    have hap : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun x => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) x
          (extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x (Y x))) :=
      ContMDiff.clm_bundle_apply
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => (Bundle.Trivial M ℝ) x)
        (b := fun x : M => x)
        (ϕ := fun x => extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x)
        (v := fun x => Y x) h_extDeriv Y.contMDiff
    intro x
    exact (contMDiffAt_section (F := ℝ) (E := Bundle.Trivial M ℝ) x).mp (hap x)
  have h_covApp : ∀ (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E (E := TangentSpace I) x (cov.toFun (fun y => V y) x (Y x))) := by
    intro V
    have hcovV : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun x => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) x
          (cov.toFun (fun y => V y) x)) :=
      cotangentCov_covApply_smooth cov V.contMDiff
    exact ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x)
      (b := fun x : M => x) (ϕ := fun x => cov.toFun (fun y => V y) x)
      (v := fun x => Y x) hcovV Y.contMDiff
  have h_t1 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => S x (cov.toFun Z x (Y x)) (W x) (U x)) :=
    tensor03_pairing_contMDiff hS (h_covApp Z) W.contMDiff U.contMDiff
  have h_t2 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => S x (Z x) (cov.toFun W x (Y x)) (U x)) :=
    tensor03_pairing_contMDiff hS Z.contMDiff (h_covApp W) U.contMDiff
  have h_t3 : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => S x (Z x) (W x) (cov.toFun U x (Y x))) :=
    tensor03_pairing_contMDiff hS Z.contMDiff W.contMDiff (h_covApp U)
  have h_combined : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => extDerivFun (I := I) (fun b => S b (Z b) (W b) (U b)) x (Y x)
        - S x (cov.toFun Z x (Y x)) (W x) (U x)
        - S x (Z x) (cov.toFun W x (Y x)) (U x)
        - S x (Z x) (W x) (cov.toFun U x (Y x))) :=
    ((h_extDeriv_Y.sub h_t1).sub h_t2).sub h_t3
  exact h_combined.congr (fun x => h_eq x)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in






omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private theorem tensor03Cov_output_contMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))) ∞
      (fun x : M => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) x
        ((tensor03Cov cov).toFun S x)) := by
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ]
      (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))
    (φ := fun x => (tensor03Cov cov).toFun S x)
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ))
    (φ := fun x => (tensor03Cov cov).toFun S x (Y x))
  intro Z
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x => (tensor03Cov cov).toFun S x (Y x) (Z x))
  intro W
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x => (tensor03Cov cov).toFun S x (Y x) (Z x) (W x))
  intro U
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => ((((tensor03Cov cov).toFun S x (Y x)) (Z x)) (W x)) (U x)) :=
    tensor03Cov_quad_apply_smooth cov hS Y Z W U
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change ((((tensor03Cov cov).toFun S y (Y y)) (Z y)) (W y)) (U y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x
      ⟨y, ((((tensor03Cov cov).toFun S y (Y y)) (Z y)) (W y)) (U y)⟩).2
  rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in




omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensor02CovIterate_metric_contMDiff
    (g₀ g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))) ∞
      (fun x : M => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) x
        (tensor02CovIterate (LeviCivita (I := I) g₀) (metricTensor02 (I := I) g) x)) := by
  haveI hcov : CovariantDerivative.ContMDiffCovariantDerivative
      (LeviCivita (I := I) g₀) ∞ := inferInstance
  have h_metric : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) := g.contMDiff
  have h_le : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) + 1 := by rw [ENat.coe_top_add_one]
  have h_metric₁ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((∞ : WithTop ℕ∞) + 1)
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) Set.univ :=
    contMDiffOn_univ.mpr (h_metric.of_le h_le)
  have hS₃ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        ((tensor02Cov (LeviCivita (I := I) g₀)).toFun (metricTensor02 (I := I) g) x)) :=
    contMDiffOn_univ.mp
      ((tensor02Cov_isContMDiff (LeviCivita (I := I) g₀)).contMDiff.contMDiff
        (σ := metricTensor02 (I := I) g) h_metric₁)
  exact tensor03Cov_output_contMDiff (LeviCivita (I := I) g₀) hS₃

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in




omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensor02Cov_metric_contMDiff
    (g₀ g : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        ((tensor02Cov (LeviCivita (I := I) g₀)).toFun (metricTensor02 (I := I) g) x)) := by
  have h_metric : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) := g.contMDiff
  have h_le : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) + 1 := by rw [ENat.coe_top_add_one]
  have h_metric₁ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ((∞ : WithTop ℕ∞) + 1)
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricTensor02 (I := I) g b)) Set.univ :=
    contMDiffOn_univ.mpr (h_metric.of_le h_le)
  exact contMDiffOn_univ.mp
    ((tensor02Cov_isContMDiff (LeviCivita (I := I) g₀)).contMDiff.contMDiff
      (σ := metricTensor02 (I := I) g) h_metric₁)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in





omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private theorem continuous_riemannian_fiber_norm_of_continuous_section
    {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
    {V₀ : M → Type*} [∀ x, NormedAddCommGroup (V₀ x)] [∀ x, InnerProductSpace ℝ (V₀ x)]
    [TopologicalSpace (TotalSpace F₀ V₀)] [FiberBundle F₀ V₀] [VectorBundle ℝ F₀ V₀]
    [IsContinuousRiemannianBundle F₀ V₀]
    {σ : Π x : M, V₀ x}
    (hσ : Continuous (fun x : M => TotalSpace.mk' F₀ (E := V₀) x (σ x))) :
    Continuous (fun x : M => ‖σ x‖) := by
  have h_inner : Continuous (fun x : M => (inner ℝ (σ x) (σ x) : ℝ)) :=
    Continuous.inner_bundle (F := F₀) (E := V₀) hσ hσ
  have h_eq : (fun x : M => ‖σ x‖) = fun x : M => Real.sqrt (inner ℝ (σ x) (σ x)) := by
    funext x
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [h_eq]
  exact Real.continuous_sqrt.comp h_inner




omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem tensor02_pairing_contMDiff
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b)))
    {Y Z : Π x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Y b)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Z b))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => S b (Y b) (Z b)) := by
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (S b (Y b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
      (b := fun b : M => b) (ϕ := fun b => S b) (v := fun b => Y b) hS hY
  have h2 : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun b : M => TotalSpace.mk' ℝ (E := fun _ : M => ℝ) b (S b (Y b) (Z b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun _ : M => ℝ)
      (b := fun b : M => b) (ϕ := fun b => S b (Y b)) (v := fun b => Z b) h1 hZ
  intro x
  exact (contMDiffAt_section (F := ℝ) (E := fun _ : M => ℝ) x).mp (h2 x)





omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem tensor04_pairing_contMDiff
    {S : Π x : M, TangentSpace I x →L[ℝ]
      (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) b (S b)))
    {Y Z W U : Π x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Y b)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Z b)))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (W b)))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (U b))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => S b (Y b) (Z b) (W b) (U b)) := by
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b (Y b))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M =>
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      (b := fun b : M => b) (ϕ := fun b => S b) (v := fun b => Y b) hS hY
  exact tensor03_pairing_contMDiff h1 hZ hW hU





omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem chartFrame_component_contMDiffOn_aux
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b)))
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => S x (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x))
      (chartAt H α).source := by
  classical
  intro x₀ hx₀
  have h_frame_on : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E b (chartFrameVec (I := I) α k b))
        (chartAt H α).source := fun k => chartAlphaFrame_section_contMDiffOn (I := I) α k
  obtain ⟨Sf, hSf_eq⟩ :=
    exists_contMDiffSection_eqOn_nhd
      (s := fun k : Fin (Module.finrank ℝ E) => fun b : M => chartFrameVec (I := I) α k b)
      (u := (chartAt H α).source) (p := x₀)
      h_frame_on ((chartAt H α).open_source) hx₀
  have hSf_smooth : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => TotalSpace.mk' E b ((Sf k) b : TangentSpace I b)) :=
    fun k => (Sf k).contMDiff
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun b : M => S b ((Sf i) b) ((Sf j) b)) :=
    tensor02_pairing_contMDiff hS (hSf_smooth i) (hSf_smooth j)
  have h_chart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => S x (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)) x₀ := by
    refine (h_scalar x₀).congr_of_eventuallyEq ?_
    filter_upwards [hSf_eq] with b hb
    rw [hb i, hb j]
  exact h_chart_at.contMDiffWithinAt



omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem metricDiff02_contMDiff (g₁ g₂ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricDiff02 (I := I) g₁ g₂ b)) := by
  have hsub :
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (metricDiff02 (I := I) g₁ g₂ b)) =
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (g₁.inner b - g₂.inner b)) := by
    funext c; rfl
  rw [hsub]
  exact g₁.contMDiff.sub_section g₂.contMDiff



private def metricDiff02ModelFun (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x :=
  Tensor0SSpace.ofModel (I := I)
    (biForm₂ToModel (TangentSpace I x) (metricDiff02 (I := I) g₁ g₂ x))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem metricDiff02ModelFun_toModel_apply
    (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (metricDiff02ModelFun (I := I) g₁ g₂ x) v =
      metricDiff02 (I := I) g₁ g₂ x (v 0) (v 1) := by
  unfold metricDiff02ModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact biForm₂ToModel_apply (TangentSpace I x) (metricDiff02 (I := I) g₁ g₂ x) v



def metricDiff02Field (g₁ g₂ : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => metricDiff02ModelFun (I := I) g₁ g₂ x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M => metricDiff02 (I := I) g₁ g₂ x
          (chartFrameVec (I := I) x₀ (σ 0) x) (chartFrameVec (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source :=
      chartFrame_component_contMDiffOn_aux (I := I)
        (metricDiff02_contMDiff (I := I) g₁ g₂) x₀ (σ 0) (σ 1)
    have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
      (chartAt H x₀).open_source.mem_nhds hx₀_src
    refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
    have h_base_nhd :
        (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
      (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
    filter_upwards [h_base_nhd] with x hx
    rw [continuousMultilinearMap_basis_repr]
    change Tensor0SSpace.toModel (metricDiff02ModelFun (I := I) g₁ g₂ x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [metricDiff02ModelFun_toModel_apply]
    rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem metricDiff02Field_toModel_apply
    (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (metricDiff02Field (I := I) g₁ g₂ x) v =
      metricDiff02 (I := I) g₁ g₂ x (v 0) (v 1) :=
  metricDiff02ModelFun_toModel_apply (I := I) g₁ g₂ x v

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in



omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem metricDiff02Cov_contMDiff (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        (metricDiff02Cov (I := I) g₀ g₁ g₂ x)) := by
  have hsub :
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        (metricDiff02Cov (I := I) g₀ g₁ g₂ x)) =
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        ((tensor02Cov (LeviCivita (I := I) g₀)).toFun (metricTensor02 (I := I) g₁) x
          - (tensor02Cov (LeviCivita (I := I) g₀)).toFun (metricTensor02 (I := I) g₂) x)) := by
    funext c
    exact congrArg _ (metricDiff02Cov_eq_sub (I := I) g₀ g₁ g₂ c)
  rw [hsub]
  exact (tensor02Cov_metric_contMDiff (I := I) g₀ g₁).sub_section
    (tensor02Cov_metric_contMDiff (I := I) g₀ g₂)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem chartFrame_component3_contMDiffOn_aux
    {S : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M =>
          TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (S b)))
    (α : M) (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => S x (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)
        (chartFrameVec (I := I) α k x))
      (chartAt H α).source := by
  classical
  intro x₁ hx₁
  have h_frame_on : ∀ m : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun c : M => TotalSpace.mk' E c (chartFrameVec (I := I) α m c))
        (chartAt H α).source := fun m => chartAlphaFrame_section_contMDiffOn (I := I) α m
  obtain ⟨Sf, hSf_eq⟩ :=
    exists_contMDiffSection_eqOn_nhd
      (s := fun m : Fin (Module.finrank ℝ E) => fun c : M => chartFrameVec (I := I) α m c)
      (u := (chartAt H α).source) (p := x₁)
      h_frame_on ((chartAt H α).open_source) hx₁
  have hSf_smooth : ∀ m : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun c : M => TotalSpace.mk' E c ((Sf m) c : TangentSpace I c)) :=
    fun m => (Sf m).contMDiff
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun c : M => S c ((Sf i) c) ((Sf j) c) ((Sf k) c)) :=
    tensor03_pairing_contMDiff hS (hSf_smooth i) (hSf_smooth j) (hSf_smooth k)
  have h_chart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => S x (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)
        (chartFrameVec (I := I) α k x)) x₁ := by
    refine (h_scalar x₁).congr_of_eventuallyEq ?_
    filter_upwards [hSf_eq] with c hc
    rw [hc i, hc j, hc k]
  exact h_chart_at.contMDiffWithinAt



private def metricDiff02CovModelFun (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 3 I x :=
  Tensor0SSpace.ofModel (I := I)
    (triFormToModel (TangentSpace I x) (metricDiff02Cov (I := I) g₀ g₁ g₂ x))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [T2Space M] [SigmaCompactSpace M] in
private theorem metricDiff02CovModelFun_toModel_apply
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel (metricDiff02CovModelFun (I := I) g₀ g₁ g₂ x) v =
      metricDiff02Cov (I := I) g₀ g₁ g₂ x (v 0) (v 1) (v 2) := by
  unfold metricDiff02CovModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact triFormToModel_apply (TangentSpace I x) (metricDiff02Cov (I := I) g₀ g₁ g₂ x) v

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in


def metricDiff02CovField (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 3 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 3
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => metricDiff02CovModelFun (I := I) g₀ g₁ g₂ x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M => metricDiff02Cov (I := I) g₀ g₁ g₂ x
          (chartFrameVec (I := I) x₀ (σ 0) x) (chartFrameVec (I := I) x₀ (σ 1) x)
          (chartFrameVec (I := I) x₀ (σ 2) x))
        (chartAt H x₀).source :=
      chartFrame_component3_contMDiffOn_aux (I := I)
        (metricDiff02Cov_contMDiff (I := I) g₀ g₁ g₂) x₀ (σ 0) (σ 1) (σ 2)
    have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
      (chartAt H x₀).open_source.mem_nhds hx₀_src
    refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
    have h_base_nhd :
        (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
      (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
    filter_upwards [h_base_nhd] with x hx
    rw [continuousMultilinearMap_basis_repr]
    change Tensor0SSpace.toModel (metricDiff02CovModelFun (I := I) g₀ g₁ g₂ x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [metricDiff02CovModelFun_toModel_apply]
    rfl⟩

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem metricDiff02CovField_toModel_apply
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel (metricDiff02CovField (I := I) g₀ g₁ g₂ x) v =
      metricDiff02Cov (I := I) g₀ g₁ g₂ x (v 0) (v 1) (v 2) :=
  metricDiff02CovModelFun_toModel_apply (I := I) g₀ g₁ g₂ x v

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in



omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem metricDiff02CovIterate_contMDiff (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) x
        (metricDiff02CovIterate (I := I) g₀ g₁ g₂ x)) := by
  have hS₁ := tensor02CovIterate_metric_contMDiff (I := I) g₀ g₁
  have hS₂ := tensor02CovIterate_metric_contMDiff (I := I) g₀ g₂
  have hsub :
      (fun x : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) x
        (metricDiff02CovIterate (I := I) g₀ g₁ g₂ x)) =
      (fun x : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) x
        (tensor02CovIterate (LeviCivita (I := I) g₀) (metricTensor02 (I := I) g₁) x
          - tensor02CovIterate (LeviCivita (I := I) g₀) (metricTensor02 (I := I) g₂) x)) := by
    funext c
    exact congrArg _ (metricDiff02CovIterate_eq_sub (I := I) g₀ g₁ g₂ c)
  rw [hsub]
  exact hS₁.sub_section hS₂

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem chartFrame_component4_contMDiffOn_aux
    {S : Π x : M, TangentSpace I x →L[ℝ]
      (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))}
    (hS : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))))
        (E := fun x : M => TangentSpace I x →L[ℝ]
          (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)))) b (S b)))
    (α : M) (i j k l : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun x : M => S x (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)
        (chartFrameVec (I := I) α k x) (chartFrameVec (I := I) α l x))
      (chartAt H α).source := by
  classical
  intro x₁ hx₁
  have h_frame_on : ∀ m : Fin (Module.finrank ℝ E),
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun c : M => TotalSpace.mk' E c (chartFrameVec (I := I) α m c))
        (chartAt H α).source := fun m => chartAlphaFrame_section_contMDiffOn (I := I) α m
  obtain ⟨Sf, hSf_eq⟩ :=
    exists_contMDiffSection_eqOn_nhd
      (s := fun m : Fin (Module.finrank ℝ E) => fun c : M => chartFrameVec (I := I) α m c)
      (u := (chartAt H α).source) (p := x₁)
      h_frame_on ((chartAt H α).open_source) hx₁
  have hSf_smooth : ∀ m : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun c : M => TotalSpace.mk' E c ((Sf m) c : TangentSpace I c)) :=
    fun m => (Sf m).contMDiff
  have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun c : M => S c ((Sf i) c) ((Sf j) c) ((Sf k) c) ((Sf l) c)) :=
    tensor04_pairing_contMDiff hS (hSf_smooth i) (hSf_smooth j) (hSf_smooth k) (hSf_smooth l)
  have h_chart_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => S x (chartFrameVec (I := I) α i x) (chartFrameVec (I := I) α j x)
        (chartFrameVec (I := I) α k x) (chartFrameVec (I := I) α l x)) x₁ := by
    refine (h_scalar x₁).congr_of_eventuallyEq ?_
    filter_upwards [hSf_eq] with c hc
    rw [hc i, hc j, hc k, hc l]
  exact h_chart_at.contMDiffWithinAt



private def metricDiff02CovIterateModelFun (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 4 I x :=
  Tensor0SSpace.ofModel (I := I)
    (quadFormToModel (TangentSpace I x) (metricDiff02CovIterate (I := I) g₀ g₁ g₂ x))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [T2Space M] [SigmaCompactSpace M] in
private theorem metricDiff02CovIterateModelFun_toModel_apply
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (v : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel (metricDiff02CovIterateModelFun (I := I) g₀ g₁ g₂ x) v =
      metricDiff02CovIterate (I := I) g₀ g₁ g₂ x (v 0) (v 1) (v 2) (v 3) := by
  unfold metricDiff02CovIterateModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact quadFormToModel_apply (TangentSpace I x) (metricDiff02CovIterate (I := I) g₀ g₁ g₂ x) v

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in


def metricDiff02CovIterateField (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 4 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => metricDiff02CovIterateModelFun (I := I) g₀ g₁ g₂ x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M => metricDiff02CovIterate (I := I) g₀ g₁ g₂ x
          (chartFrameVec (I := I) x₀ (σ 0) x) (chartFrameVec (I := I) x₀ (σ 1) x)
          (chartFrameVec (I := I) x₀ (σ 2) x) (chartFrameVec (I := I) x₀ (σ 3) x))
        (chartAt H x₀).source :=
      chartFrame_component4_contMDiffOn_aux (I := I)
        (metricDiff02CovIterate_contMDiff (I := I) g₀ g₁ g₂) x₀ (σ 0) (σ 1) (σ 2) (σ 3)
    have hx₀_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have hx₀_base : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have h_src_nhd : (chartAt H x₀).source ∈ 𝓝 x₀ :=
      (chartAt H x₀).open_source.mem_nhds hx₀_src
    refine ((hcomp x₀ hx₀_src).contMDiffAt h_src_nhd).congr_of_eventuallyEq ?_
    have h_base_nhd :
        (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝 x₀ :=
      (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds hx₀_base
    filter_upwards [h_base_nhd] with x hx
    rw [continuousMultilinearMap_basis_repr]
    change Tensor0SSpace.toModel (metricDiff02CovIterateModelFun (I := I) g₀ g₁ g₂ x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [metricDiff02CovIterateModelFun_toModel_apply]
    rfl⟩

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem metricDiff02CovIterateField_toModel_apply
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) (v : Fin 4 → TangentSpace I x) :
    Tensor0SSpace.toModel (metricDiff02CovIterateField (I := I) g₀ g₁ g₂ x) v =
      metricDiff02CovIterate (I := I) g₀ g₁ g₂ x (v 0) (v 1) (v 2) (v 3) :=
  metricDiff02CovIterateModelFun_toModel_apply (I := I) g₀ g₁ g₂ x v



def metricDiff02MixedSection (g₁ g₂ : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (metricDiff02Field (I := I) g₁ g₂)



def metricDiff02CovMixedSection (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 3 ℝ E, (fun x : M => TensorRSSpace 0 3 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (metricDiff02CovField (I := I) g₀ g₁ g₂)



def metricDiff02CovIterateMixedSection (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 4 ℝ E, (fun x : M => TensorRSSpace 0 4 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (metricDiff02CovIterateField (I := I) g₀ g₁ g₂)

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in








def metricDiff2JetNorm (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) : ℝ :=
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  ‖metricDiff02MixedSection (I := I) g₁ g₂ x‖
    + ‖metricDiff02CovMixedSection (I := I) g₀ g₁ g₂ x‖
    + ‖metricDiff02CovIterateMixedSection (I := I) g₀ g₁ g₂ x‖

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricDiff2JetNorm_eq_riemannianNorm_sum
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
    metricDiff2JetNorm (I := I) g₀ g₁ g₂ x =
      ‖metricDiff02MixedSection (I := I) g₁ g₂ x‖
        + ‖metricDiff02CovMixedSection (I := I) g₀ g₁ g₂ x‖
        + ‖metricDiff02CovIterateMixedSection (I := I) g₀ g₁ g₂ x‖ :=
  rfl

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricDiff2JetNorm_nonneg
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    0 ≤ metricDiff2JetNorm (I := I) g₀ g₁ g₂ x := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  rw [metricDiff2JetNorm_eq_riemannianNorm_sum (I := I) g₀ g₁ g₂ x]
  have := norm_nonneg (metricDiff02MixedSection (I := I) g₁ g₂ x)
  have := norm_nonneg (metricDiff02CovMixedSection (I := I) g₀ g₁ g₂ x)
  have := norm_nonneg (metricDiff02CovIterateMixedSection (I := I) g₀ g₁ g₂ x)
  positivity

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Bundle.continuousMultilinearMap.mixed_instNormedAddCommGroup
  Bundle.continuousMultilinearMap.mixed_instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in







omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricDiff2JetNorm_continuous
    (g₀ g₁ g₂ : SmoothRiemannianMetric I M) :
    Continuous (fun x : M => metricDiff2JetNorm (I := I) g₀ g₁ g₂ x) := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 4 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 4
  haveI hC2 : IsContinuousRiemannianBundle (TensorRSModel 0 2 ℝ E)
      (fun b : M => TensorRSSpace 0 2 I b) :=
    DifferentialGeometry.Tensor.TensorRSRiemannianBundleContinuous.tensorRS_isContinuousRiemannianBundle
      (I := I) (M := M) g₀ 0 2
  haveI hC3 : IsContinuousRiemannianBundle (TensorRSModel 0 3 ℝ E)
      (fun b : M => TensorRSSpace 0 3 I b) :=
    DifferentialGeometry.Tensor.TensorRSRiemannianBundleContinuous.tensorRS_isContinuousRiemannianBundle
      (I := I) (M := M) g₀ 0 3
  haveI hC4 : IsContinuousRiemannianBundle (TensorRSModel 0 4 ℝ E)
      (fun b : M => TensorRSSpace 0 4 I b) :=
    DifferentialGeometry.Tensor.TensorRSRiemannianBundleContinuous.tensorRS_isContinuousRiemannianBundle
      (I := I) (M := M) g₀ 0 4
  have h0 : Continuous (fun x : M => ‖metricDiff02MixedSection (I := I) g₁ g₂ x‖) :=
    continuous_riemannian_fiber_norm_of_continuous_section
      (F₀ := TensorRSModel 0 2 ℝ E) (V₀ := fun b : M => TensorRSSpace 0 2 I b)
      (σ := fun x => metricDiff02MixedSection (I := I) g₁ g₂ x)
      (metricDiff02MixedSection (I := I) g₁ g₂).contMDiff.continuous
  have h1 : Continuous (fun x : M => ‖metricDiff02CovMixedSection (I := I) g₀ g₁ g₂ x‖) :=
    continuous_riemannian_fiber_norm_of_continuous_section
      (F₀ := TensorRSModel 0 3 ℝ E) (V₀ := fun b : M => TensorRSSpace 0 3 I b)
      (σ := fun x => metricDiff02CovMixedSection (I := I) g₀ g₁ g₂ x)
      (metricDiff02CovMixedSection (I := I) g₀ g₁ g₂).contMDiff.continuous
  have h2 : Continuous (fun x : M => ‖metricDiff02CovIterateMixedSection (I := I) g₀ g₁ g₂ x‖) :=
    continuous_riemannian_fiber_norm_of_continuous_section
      (F₀ := TensorRSModel 0 4 ℝ E) (V₀ := fun b : M => TensorRSSpace 0 4 I b)
      (σ := fun x => metricDiff02CovIterateMixedSection (I := I) g₀ g₁ g₂ x)
      (metricDiff02CovIterateMixedSection (I := I) g₀ g₁ g₂).contMDiff.continuous
  have hsum := (h0.add h1).add h2
  refine hsum.congr (fun x => ?_)
  rw [metricDiff2JetNorm_eq_riemannianNorm_sum (I := I) g₀ g₁ g₂ x]
  simp only [Pi.add_apply]





def chartDeTurckRHSComp (g_bg g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (-2 : ℝ) * chartRicciTensor (I := I) g α i j y
    + chartLieDeTurckComp (I := I) g g_bg α i j y

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem chartDeTurckRHSComp_def (g_bg g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartDeTurckRHSComp (I := I) g_bg g α i j y =
      (-2 : ℝ) * chartRicciTensor (I := I) g α i j y
        + chartLieDeTurckComp (I := I) g g_bg α i j y := rfl



























omit [CompactSpace M] in
omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem exists_chartDeTurckRHSComp_lipschitz_on_compact
    (g_bg g₁ g₂ : SmoothRiemannianMetric I M) (α : M)
    {K : Set E} (hK : IsCompact K)
    (hKsub : K ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, ∀ i j : Fin (Module.finrank ℝ E),
      |chartDeTurckRHSComp (I := I) g_bg g₁ α i j y -
          chartDeTurckRHSComp (I := I) g_bg g₂ α i j y| ≤
        C * chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y := by
  classical
  obtain ⟨Cric, hCric_pos, hCric⟩ :=
    DeTurckCoefficients.exists_chartRicciTensor_lipschitz_on_compact
      (I := I) (M := M) g₁ g₂ α hK hKsub
  obtain ⟨Clie, hClie_pos, hClie⟩ :=
    DeTurckCoefficients.exists_chartLieDeTurckComp_lipschitz_on_compact
      (I := I) (M := M) g₁ g₂ g_bg α hK hKsub
  refine ⟨2 * Cric + Clie, ?_, ?_⟩
  · have h1 : 0 < 2 * Cric := by positivity
    linarith
  intro y hy i j
  have hjet2_nn : 0 ≤ chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y :=
    DeTurckCoefficients.chartMetricJet2DiffSup_nonneg _ _ _ _
  set jet2 : ℝ := chartMetricJet2DiffSup (I := I) (M := M) g₁ g₂ α y with hjet2_def
  have hsplit :
      chartDeTurckRHSComp (I := I) g_bg g₁ α i j y -
          chartDeTurckRHSComp (I := I) g_bg g₂ α i j y =
        (-2 : ℝ) * (chartRicciTensor (I := I) g₁ α i j y -
              chartRicciTensor (I := I) g₂ α i j y)
          + (chartLieDeTurckComp (I := I) g₁ g_bg α i j y -
              chartLieDeTurckComp (I := I) g₂ g_bg α i j y) := by
    rw [chartDeTurckRHSComp_def, chartDeTurckRHSComp_def]; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have hric_bound : |(-2 : ℝ) * (chartRicciTensor (I := I) g₁ α i j y -
        chartRicciTensor (I := I) g₂ α i j y)| ≤ 2 * Cric * jet2 := by
    rw [abs_mul]
    have h2 : |(-2 : ℝ)| = 2 := by norm_num
    rw [h2]
    have hR := hCric y hy i j
    calc 2 * |chartRicciTensor (I := I) g₁ α i j y -
            chartRicciTensor (I := I) g₂ α i j y|
        ≤ 2 * (Cric * jet2) :=
          mul_le_mul_of_nonneg_left hR (by norm_num)
      _ = 2 * Cric * jet2 := by ring
  have hlie_bound : |chartLieDeTurckComp (I := I) g₁ g_bg α i j y -
        chartLieDeTurckComp (I := I) g₂ g_bg α i j y| ≤ Clie * jet2 :=
    hClie y hy i j
  calc |(-2 : ℝ) * (chartRicciTensor (I := I) g₁ α i j y -
            chartRicciTensor (I := I) g₂ α i j y)|
        + |chartLieDeTurckComp (I := I) g₁ g_bg α i j y -
            chartLieDeTurckComp (I := I) g₂ g_bg α i j y|
      ≤ 2 * Cric * jet2 + Clie * jet2 := add_le_add hric_bound hlie_bound
    _ = (2 * Cric + Clie) * jet2 := by ring

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
