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

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma interiorProduct_toModel_eval_dla (s : ℕ) (x : M) (vv : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from vv) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from vv)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_om_single_eq_cotangentToDual_dla (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → TangentSpace I x) :
    Tensor0SSpace.toModel om (fun k => (m k : E)) =
      cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [show (fun k : Fin 1 => (m k : E)) = (fun _ : Fin 1 => (m 0 : E)) from by
    funext k; fin_cases k; rfl]
  rw [cotangentToDual_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma cotangentToDual_eq_inner_sharp_dla (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (ww : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) om ww =
      g₀.inner x ww (inverseMetricSharpFib (I := I) g₀ x om) := by
  rw [g₀.symm x ww (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [show g₀.inner x (inverseMetricSharpFib (I := I) g₀ x om) ww =
      cotangentToDualLinear (I := I) (x := x) om ww from by
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om ww]]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma cotangentToDual_map_sub_dla (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) om (a - b) =
      cotangentToDual (I := I) (x := x) om a - cotangentToDual (I := I) (x := x) om b := by
  simp only [show ∀ v : TangentSpace I x, cotangentToDual (I := I) (x := x) om v =
      cotangentToDualLinear (I := I) (x := x) om v from fun v => rfl]
  exact map_sub _ a b

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma cotangentToDual_map_add_dla (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) om (a + b) =
      cotangentToDual (I := I) (x := x) om a + cotangentToDual (I := I) (x := x) om b := by
  simp only [show ∀ v : TangentSpace I x, cotangentToDual (I := I) (x := x) om v =
      cotangentToDualLinear (I := I) (x := x) om v from fun v => rfl]
  exact map_add _ a b

private noncomputable def deTurckLieConnDiffDerivKernelCLM (g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => connDiffCovDerivOp (I := I) g₁ g_bg x v0
      map_add' := fun v0 v0' => by
        apply ContinuousLinearMap.ext
        intro p
        apply ContinuousLinearMap.ext
        intro q
        simp only [ContinuousLinearMap.add_apply]
        exact dLaCovKernel_add_left (I := I) g₁ g_bg x v0 v0' p q
      map_smul' := fun c v0 => by
        apply ContinuousLinearMap.ext
        intro p
        apply ContinuousLinearMap.ext
        intro q
        simp only [RingHom.id_apply, ContinuousLinearMap.smul_apply]
        exact dLaCovKernel_smul_left (I := I) g₁ g_bg x c v0 p q }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma dLaCovKernelCLM_apply (g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (v0 p q : TangentSpace I x) :
    deTurckLieConnDiffDerivKernelCLM (I := I) (M := M) g₁ g_bg x v0 p q =
      connDiffCovDerivOp (I := I) g₁ g_bg x v0 p q := by
  rw [deTurckLieConnDiffDerivKernelCLM, LinearMap.coe_toContinuousLinearMap']
  rfl

private noncomputable def dLaLoweredCovec (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 4 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ from
    { toFun := fun m =>
        g₀.inner x (deTurckLieConnDiffDerivKernelCLM (I := I) (M := M) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0)
      map_update_add' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true, map_add, ContinuousLinearMap.add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true, map_smul, ContinuousLinearMap.smul_apply]
      cont := by
        have hK : Continuous (fun m : Fin 4 → TangentSpace I x =>
            deTurckLieConnDiffDerivKernelCLM (I := I) (M := M) g₁ g_bg x (m 1) (m 2) (m 3)) :=
          (((deTurckLieConnDiffDerivKernelCLM (I := I) (M := M) g₁ g_bg x).continuous.comp
            (continuous_apply 1)).clm_apply (continuous_apply 2)).clm_apply (continuous_apply 3)
        exact ((g₀.inner x).continuous.comp hK).clm_apply (continuous_apply 0) }
    : Tensor0SSpace 4 I x)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma dLaLoweredCovec_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    dLaLoweredCovec (I := I) g₀ g₁ g_bg x m =
      g₀.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) := by
  change g₀.inner x (deTurckLieConnDiffDerivKernelCLM (I := I) (M := M) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) = _
  rw [dLaCovKernelCLM_apply]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma dLaLoweredScalar_global (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    {V0 W p q : Π b : M, TangentSpace I b}
    (hV0 : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V0))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (connDiffCovDerivOp (I := I) g₁ g_bg x (V0 x) (p x) (q x)) (W x)) := by
  classical
  have hAsec := deTurckLieCovDerivA_section_contMDiff (I := I) g₁ g_bg V0 p q hV0 hp hq
  have hcongr : (fun x : M => g₀.inner x
        (connDiffCovDerivOp (I := I) g₁ g_bg x (V0 x) (p x) (q x)) (W x)) =
      (fun x : M => g₀.inner x (deTurckConnDiffCovDeriv (I := I) g₁ g_bg V0 p q x) (W x)) := by
    funext x
    rw [dLaCovKernel_apply_field3 (I := I) g₁ g_bg x V0 p q
      (hV0.contMDiffAt.mdifferentiableAt (by simp))
      (hp.contMDiffAt.mdifferentiableAt (by simp))
      (hq.contMDiffAt.mdifferentiableAt (by simp))]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₀
    ⟨fun b => deTurckConnDiffCovDeriv (I := I) g₁ g_bg V0 p q b, hAsec⟩ ⟨fun b => W b, hW⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma dLaLoweredScalar_contMDiffAt (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (V0 V1 V2 V3 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        g₀.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (V1 x) (V2 x) (V3 x)) (V0 x)) x₀ := by
  have hglob := dLaLoweredScalar_global (I := I) (M := M) g₀ g₁ g_bg
    (V0 := fun b => V1 b) (W := fun b => V0 b) (p := fun b => V2 b) (q := fun b => V3 b)
    V1.contMDiff V0.contMDiff V2.contMDiff V3.contMDiff
  exact hglob.contMDiffAt

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem dLaLoweredCovec_section_contMDiff (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) x (dLaLoweredCovec (I := I) g₀ g₁ g_bg x)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (dLaLoweredCovec (I := I) g₀ g₁ g_bg x :
        Bundle.continuousMultilinearMap ℝ 4 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (connDiffCovDerivOp (I := I) g₁ g_bg x (Y (σ 1) x) (Y (σ 2) x) (Y (σ 3) x))
        (Y (σ 0) x)) x₀ :=
    dLaLoweredScalar_contMDiffAt (I := I) (M := M) g₀ g₁ g_bg
      (Y (σ 0)) (Y (σ 1)) (Y (σ 2)) (Y (σ 3)) x₀
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframeEq : ∀ k : Fin 4, e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
    intro k
    rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change dLaLoweredCovec (I := I) g₀ g₁ g_bg x (fun k => e₁.symmL ℝ x (b (σ k))) = _
  rw [dLaLoweredCovec_apply]
  rw [hframeEq 0, hframeEq 1, hframeEq 2, hframeEq 3]

private def dLaLoweredField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 4 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  ⟨fun x => dLaLoweredCovec (I := I) g₀ g₁ g_bg x,
    dLaLoweredCovec_section_contMDiff (I := I) (M := M) g₀ g₁ g_bg⟩

def dLaLoweredCc (g₀ g₁ g_bg : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (dLaLoweredField (I := I) (M := M) g₀ g₁ g_bg)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma dLaLoweredCc_unitModel (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 4 (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x =
      Tensor0SSpace.toModel (dLaLoweredCovec (I := I) g₀ g₁ g_bg x) := by
  rw [unitModel]
  rw [show (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg).toSection x
        (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (dLaLoweredField (I := I) (M := M) g₀ g₁ g_bg x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma dLaLoweredCc_unitModel_apply (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x m =
      g₀.inner x (connDiffCovDerivOp (I := I) g₁ g_bg x (m 1) (m 2) (m 3)) (m 0) := by
  rw [dLaLoweredCc_unitModel]
  exact dLaLoweredCovec_apply (I := I) (M := M) g₀ g₁ g_bg x m

def dLaConnArmPt (g₀ gc : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => PDE.DeTurck.connDiff (I := I) gc g₀ x,
    bilinEndoField_contMDiff (I := I) (M := M)
      (fun x : M => PDE.DeTurck.connDiff (I := I) gc g₀ x)
      (fun V0 W => PDE.DeTurck.connDiff_contMDiff (I := I) gc g₀ V0.contMDiff W.contMDiff)⟩

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma dLaConnArmPt_apply (g₀ gc : SmoothRiemannianMetric I M) (x : M) :
    dLaConnArmPt (I := I) (M := M) g₀ gc x = PDE.DeTurck.connDiff (I := I) gc g₀ x := rfl

def dLaQuadCc (g₀ g_arm g_out : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 3 :=
  ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 3
    (armSlotEndoPassZeroCc (I := I) (M := M) g₀ (dLaConnArmPt (I := I) (M := M) g₀ g_arm))
    (connDiffSection (I := I) g_out g₀)

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
lemma dLaQuadCc_toModel (g₀ g_arm g_out : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (w : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (dLaQuadCc (I := I) (M := M) g₀ g_arm g_out).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) g_out g₀ x
          (PDE.DeTurck.connDiff (I := I) g_arm g₀ x (w 1) (w 2)) (w 0)) := by
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (dLaQuadCc (I := I) (M := M) g₀ g_arm g_out).toSection x) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 3
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (dLaConnArmPt (I := I) (M := M) g₀ g_arm))
          (connDiffSection (I := I) g_out g₀)).toSection x) om) from rfl]
  rw [toModel_appCcRS_armSlotEndoPassZeroCc_eval (I := I) (M := M) g₀
    (dLaConnArmPt (I := I) (M := M) g₀ g_arm) (connDiffSection (I := I) g_out g₀) x om w]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) g_out g₀).toSection x) om) =
      connDiffPairing (I := I) g_out g₀ x om from rfl]
  have hchg : Tensor0SSpace.toModel (connDiffPairing (I := I) g_out g₀ x om)
      (fun j : Fin 2 => if j = 0 then
        dLaConnArmPt (I := I) (M := M) g₀ g_arm x (w 1) (w 2) else w 0) =
      connDiffPairing (I := I) g_out g₀ x om
        (fun j : Fin 2 => if j = 0 then
          dLaConnArmPt (I := I) (M := M) g₀ g_arm x (w 1) (w 2) else w 0) := rfl
  rw [hchg]
  rw [show (fun j : Fin 2 => if j = 0 then
        dLaConnArmPt (I := I) (M := M) g₀ g_arm x (w 1) (w 2) else w 0) =
      (Fin.cons (PDE.DeTurck.connDiff (I := I) g_arm g₀ x (w 1) (w 2))
        (fun _ : Fin 1 => w 0) : Fin 2 → TangentSpace I x) from by
    funext j
    refine Fin.cases ?_ ?_ j
    · rw [if_pos rfl]
      rfl
    · intro i
      rw [if_neg (Fin.succ_ne_zero i)]
      rfl]
  rw [connDiffPairing_apply]
  rw [cotangentToDual_apply]
  rfl

def dLaKernelRaisedCc (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 3 :=
  covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)
    - covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀)
    + dLaQuadCc (I := I) (M := M) g₀ g₁ g₁
    - dLaQuadCc (I := I) (M := M) g₀ g_bg g₁
    - rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2)
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g₁)
    + rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2)
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g_bg)
    - rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g₁)
    + rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g_bg)

def dLaCovectorExtensionSection (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun y : M => Tensor0SSpace 1 I y)⟯ :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 1
  ⟨fun b : M => g0FlatCLM (I := I) g₀ b
      (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) b),
   by
     have hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
         (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
           (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) b)) :=
       smoothExtensionTangent_contMDiff (I := I) x (inverseMetricSharpFib (I := I) g₀ x om)
     exact ContMDiff.clm_bundle_apply (b := id) (g0FlatField_contMDiff (I := I) g₀) hU⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma dLaCovectorExtensionSection_self (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    dLaCovectorExtensionSection (I := I) (M := M) g₀ x om x = om := by
  change g0FlatCLM (I := I) g₀ x
      (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) x) = om
  rw [smoothExtensionTangent_eq (I := I) x (inverseMetricSharpFib (I := I) g₀ x om)]
  exact g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x om

end DLaGridBrick

end DifferentialGeometry.Integral.Connection

end
