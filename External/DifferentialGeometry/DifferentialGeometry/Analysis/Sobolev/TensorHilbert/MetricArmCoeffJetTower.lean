import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckMetricArmCoeffField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceFibreBound
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SecondBianchi
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradFibreNormPermutationInvariance
import DifferentialGeometry.Analysis.Sobolev.AntidiagonalTupleProductGrid
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTowerRaisedEndoCovariantDerivativeBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.MetricArmCoeffJetTowerSlotInsertEndoFibNormBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTowerArmSlotFibNormBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTowerAppCcRSProductGridRankLeftBound


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
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open TensorRSNabla
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (metricCauchySchwarzBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

section NormedL2Identity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toFun ^ 2 =
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hfun : S.toFun = fun x => TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
      (r := r) (s := s) (x := x) (S.toSection x) := rfl
  rw [hfun]
  exact tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g r s _

end NormedL2Identity

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem norm_le_of_pointwise_fiberNormSq_bound_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (C : SmoothCcTensor g r s) (B : ℝ)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x) ≤ B) :
    ‖C‖ ^ 2 ≤ B * (riemannianVolumeMeasure (I := I) (M := M) g Set.univ).toReal := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  rw [SmoothCcTensor.norm_def (I := I) (M := M) C,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r s C]
  have hint : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g r s C
  calc ∫ x, riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)
      ≤ ∫ _x, B ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        refine MeasureTheory.integral_mono hint (MeasureTheory.integrable_const B)
          (fun x => hpt x)
    _ = B * (riemannianVolumeMeasure (I := I) (M := M) g Set.univ).toReal := by
        rw [MeasureTheory.integral_const, smul_eq_mul,
          MeasureTheory.measureReal_def, mul_comm]

section NormedIntegralBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
theorem normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (C : SmoothCcTensor g r s) (F : M → ℝ)
    (hF_int : MeasureTheory.Integrable F (riemannianVolumeMeasure (I := I) (M := M) g))
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x) ≤ F x) :
    ‖C‖ ^ 2 ≤ ∫ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  rw [SmoothCcTensor.norm_def (I := I) (M := M) C,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g r s C]
  have hint : MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (C.toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g r s C
  exact MeasureTheory.integral_mono hint hF_int (fun x => hpt x)

end NormedIntegralBound

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_gInvDiffSlotCoeff_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
    (h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm g₀ T y v w)
    (hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm g₀ T) δ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
        ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x) ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 := by
  have hδ1 : δ < 1 := by linarith
  have hbase := riemannianFiberNormSq_gInvDiffSlotEndo_le (I := I) (M := M) g₀ g₁
    (ccTensorBilinSymm g₀ T) (fun y v w => h y v w) hδ1 hδ0 hbound x
  have hcoeff : (0 : ℝ) < 1 - δ := by linarith
  have hratio : δ / (1 - δ) ≤ 1 := by
    rw [div_le_one hcoeff]; linarith
  have hratio0 : 0 ≤ δ / (1 - δ) := div_nonneg hδ0 (by linarith)
  have hfr0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hmono : ((Module.finrank ℝ E : ℝ) * (δ / (1 - δ))) ^ 2 ≤
      ((Module.finrank ℝ E : ℝ)) ^ 2 := by
    have : (Module.finrank ℝ E : ℝ) * (δ / (1 - δ)) ≤ (Module.finrank ℝ E : ℝ) := by
      calc (Module.finrank ℝ E : ℝ) * (δ / (1 - δ))
          ≤ (Module.finrank ℝ E : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left hratio hfr0
        _ = (Module.finrank ℝ E : ℝ) := by rw [mul_one]
    nlinarith [mul_nonneg hfr0 hratio0]
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x)
      = riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          (show TensorRSSpace 2 2 I x from
            TensorRSSpace.ofCLM (metricComparisonDiffSlotEndo (I := I) g₀ g₁ x)) := by rfl
    _ ≤ ((Module.finrank ℝ E : ℝ) * (δ / (1 - δ))) ^ 2 := hbase
    _ ≤ ((Module.finrank ℝ E : ℝ)) ^ 2 := hmono

section NormedSlotCoefficientIdentity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem gInvDiffSlotCoeff_eq_slotInsertEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    gInvDiffSlotCoeff (I := I) g₀ g₁ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 (gInvDiffRaisedEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

end NormedSlotCoefficientIdentity

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem endoCompSection_contMDiff
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        ((A x).comp (B x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := E) (V₂ := fun z : M => TangentSpace I z)
    (φ := fun x => (A x).comp (B x))
  intro Y
  have hBY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((B y) (Y y))) :=
    endoApplySection_contMDiff (I := I) (M := M) B Y
  let BY : Cₛ^∞⟮I; E, (fun y : M => TangentSpace I y)⟯ := ⟨fun y : M => (B y) (Y y), hBY⟩
  have hABY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((A y) (BY y))) :=
    endoApplySection_contMDiff (I := I) (M := M) A BY
  refine hABY.congr (fun x => ?_)
  rfl

set_option backward.isDefEq.respectTransparency false in
def endoCompField (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => (A x).comp (B x)
  contMDiff_toFun := endoCompSection_contMDiff (I := I) (M := M) A B

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma endoCompField_apply
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) (x : M) :
    (endoCompField (I := I) (M := M) A B x) = (A x).comp (B x) := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem endoCovariantDerivative_comp
    (g₀ : SmoothRiemannianMetric I M)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (endoCompField (I := I) (M := M) A B) x v) =
      ((endoCovariantDerivative (I := I) (M := M) g₀) A x v).comp (B x) +
        (A x).comp ((endoCovariantDerivative (I := I) (M := M) g₀) B x v) := by
  classical
  apply ContinuousLinearMap.ext
  intro a
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x a
  have hBY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y ((B y) (Y y))) :=
    endoApplySection_contMDiff (I := I) (M := M) B Y
  let BY : Cₛ^∞⟮I; E, (fun y : M => TangentSpace I y)⟯ := ⟨fun y : M => (B y) (Y y), hBY⟩
  have hYmd := Y.mdifferentiableAt (x := x)
  have hABcomp := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (endoCompField (I := I) (M := M) A B) Y x v
  have hAonBY := endoCovariantDerivative_apply (I := I) (M := M) g₀ A BY x v
  have hBonY := endoCovariantDerivative_apply (I := I) (M := M) g₀ B Y x v
  have hfun_eq : (fun y : M => (endoCompField (I := I) (M := M) A B y) (Y y)) =
      (fun y : M => (A y) ((B y) (Y y))) := by
    funext y
    rw [endoCompField_apply, ContinuousLinearMap.comp_apply]
  have hcompval : ((endoCovariantDerivative (I := I) (M := M) g₀)
        (endoCompField (I := I) (M := M) A B) x v) (Y x) =
      (LeviCivita (I := I) g₀) (fun y : M => (A y) ((B y) (Y y))) x v -
        (endoCompField (I := I) (M := M) A B x) ((LeviCivita (I := I) g₀) (fun y => Y y) x v) := by
    rw [hABcomp, hfun_eq]
  have hgradY : (LeviCivita (I := I) g₀) (fun y => Y y) x v =
      (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v := rfl
  have hBgrad : (LeviCivita (I := I) g₀) (fun y : M => (B y) (Y y)) x v =
      ((endoCovariantDerivative (I := I) (M := M) g₀) B x v) (Y x) +
        (B x) ((LeviCivita (I := I) g₀) (fun y => Y y) x v) := by
    rw [eq_sub_iff_add_eq] at hBonY
    rw [← hBonY]
  have hAonBY' : ((endoCovariantDerivative (I := I) (M := M) g₀) A x v) ((B x) (Y x)) =
      (LeviCivita (I := I) g₀) (fun y : M => (A y) ((B y) (Y y))) x v -
        (A x) ((LeviCivita (I := I) g₀) (fun y : M => (B y) (Y y)) x v) := hAonBY
  rw [← hYx]
  rw [hcompval]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, endoCompField_apply, ContinuousLinearMap.comp_apply]
  rw [hAonBY', hBgrad, map_add]
  abel

section HilbertFirstDerivativeBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem riemannianFiberNormSq_covGrad_gInvDiffSlotCoeff_le
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M)
      (T : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (_hδ : δ < 1 / 2) (_hδ0 : 0 ≤ δ)
      (_h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      (x : M),
      letI : Bundle.RiemannianBundle
          (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
          ((covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
        C ^ 2 * ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
            Tensor0SBundle.TensorRSSpace 0 3 I x)‖ ^ 2 := by
  classical
  letI instTens : Bundle.RiemannianBundle
      (fun y : M => Tensor0SBundle.TensorRSSpace 0 3 I y) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  obtain ⟨C₀, hC₀0, hpw⟩ := sqrt_inner_endoCov_gInvDiffRaisedField_le (I := I) (M := M) g₀
  refine ⟨Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * (4 * C₀), by positivity, ?_⟩
  intro g₁ T δ hδ hδ0 h hbound x
  set Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) :=
    gInvDiffRaisedEndoField (I := I) g₀ g₁ with hΛ_def
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 3 I x)‖ with hG_def
  have hG_nn : 0 ≤ G := norm_nonneg _
  rw [gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g₀ g₁, ← hΛ_def]
  rw [covGrad_toSection_apply (I := I) (M := M) g₀ 2 2
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 Λ) x]
  refine le_trans (DifferentialGeometry.Analysis.Sobolev.Tensor.riemannianFiberNormSq_covGradBundleEquiv_le_card_mul_rs (I := I) (M := M)
    g₀ 2 2 x _ ((Module.finrank ℝ E : ℝ) ^ 2 * (4 * C₀ * G) ^ 2) ?_) ?_
  · intro v hv
    have hΦ : tensorRSCovariantDerivative I M 2 2 (LeviCivita (I := I) g₀)
          (fun y : M => (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 Λ).toSection y) x v =
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (slotInsertEndoFib (I := I) (M := M) 2 0 x
            ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v))) := by
      rw [← tensorCovDerivAt_def (I := I) (M := M) g₀ 2 2
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 Λ) x v]
      exact tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ 1 Λ x v
    rw [hΦ]
    refine riemannianFiberNormSq_slotInsertEndoFib_le_card_mul (I := I) g₀ x
      ((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) ((4 * C₀ * G) ^ 2) ?_ (by positivity)
    intro a ha
    obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x a
    have hbd := hpw g₁ T h hδ hδ0 hbound Y x v
    rw [hYx] at hbd
    have hvroot : Real.sqrt (g₀.inner x v v) = 1 := by rw [hv, Real.sqrt_one]
    have haroot : Real.sqrt (g₀.inner x a a) = 1 := by rw [ha, Real.sqrt_one]
    rw [hvroot, haroot, mul_one, mul_one, ← hG_def] at hbd
    have haa_nn : 0 ≤ g₀.inner x
        (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a)
        (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a) :=
      metric_inner_self_nonneg (I := I) (M := M) g₀ x _
    have hsq := Real.sq_sqrt haa_nn
    nlinarith [hbd, Real.sqrt_nonneg (g₀.inner x
      (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a)
      (((endoCovariantDerivative (I := I) (M := M) g₀) Λ x v) a)), hsq,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC₀0) hG_nn]
  · have hsq3 : Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) ^ 2 = (Module.finrank ℝ E : ℝ) ^ 3 :=
      Real.sq_sqrt (by positivity)
    have hrhs : (Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 3) * (4 * C₀)) ^ 2 * G ^ 2 =
        (Module.finrank ℝ E : ℝ) ^ 3 * (4 * C₀ * G) ^ 2 := by
      rw [mul_pow, hsq3]; ring
    have hlhs : (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) ^ 2 * (4 * C₀ * G) ^ 2) =
        (Module.finrank ℝ E : ℝ) ^ 3 * (4 * C₀ * G) ^ 2 := by ring
    rw [hlhs, hrhs]

end HilbertFirstDerivativeBound

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem norm_toSection_eq_sqrt_riemannianFiberNormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (W : SmoothCcTensor g r s) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ‖(W.toSection x : TensorRSSpace r s I x)‖ =
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s x (W.toSection x)) := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  rw [norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g r s x (W.toSection x),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (W.toSection x)]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_iteratedCovGrad_gInvDiffSlotCoeff_le_envelope_zero
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ : δ < 1 / 2) (hδ0 : 0 ≤ δ)
    (h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) (x : M) (R : ℝ) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 2 I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 2
    ‖((iteratedCovGrad (I := I) g₀ 2 2 0 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x :
        TensorRSSpace 2 2 I x)‖ ≤
      (Module.finrank ℝ E : ℝ) * (1 + R) ^ 0 := by
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 2
  rw [iteratedCovGrad_zero, pow_zero, mul_one,
    norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      (gInvDiffSlotCoeff (I := I) g₀ g₁)]
  have hb := riemannianFiberNormSq_gInvDiffSlotCoeff_le (I := I) (M := M) g₀ g₁ T hδ hδ0 h hbound x
  have hfr0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
          ((gInvDiffSlotCoeff (I := I) g₀ g₁).toSection x))
      ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 2) := Real.sqrt_le_sqrt hb
    _ = (Module.finrank ℝ E : ℝ) := Real.sqrt_sq hfr0

section HilbertFirstDerivativeEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
theorem norm_iteratedCovGrad_gInvDiffSlotCoeff_le_envelope_one
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (_hδ : δ < 1 / 2) (_hδ0 : 0 ≤ δ)
      (_h : ∀ y v w, g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
      (_hbound : metricCauchySchwarzBound (I := I) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) (x : M) {R : ℝ}
      (_hR0 : 0 ≤ R)
      (_hjet : letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
          Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
        ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x : TensorRSSpace 0 3 I x)‖ ≤ R),
      letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 3 I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 3
      ‖((iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x :
          TensorRSSpace 2 3 I x)‖ ≤ C * (1 + R) ^ 1 := by
  obtain ⟨C, hC0, hbnd⟩ := riemannianFiberNormSq_covGrad_gInvDiffSlotCoeff_le (I := I) (M := M) g₀
  refine ⟨C, hC0, ?_⟩
  intro g₁ T δ hδ hδ0 h hbound x R hR0 hjet
  letI inst3 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 3
  letI inst23 : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 2 3 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 2 3
  have hb := hbnd g₁ T hδ hδ0 h hbound x
  have hiter1 : iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁) =
      covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁) := by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  rw [pow_one,
    norm_toSection_eq_sqrt_riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
      (iteratedCovGrad (I := I) g₀ 2 2 1 (gInvDiffSlotCoeff (I := I) g₀ g₁)), hiter1]
  set G : ℝ := ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x : TensorRSSpace 0 3 I x)‖ with hG
  have hG0 : 0 ≤ G := norm_nonneg _
  have hsqrt_le : Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ 2 3 x
      ((covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x)) ≤
      Real.sqrt (C ^ 2 * G ^ 2) := Real.sqrt_le_sqrt hb
  refine hsqrt_le.trans ?_
  rw [show C ^ 2 * G ^ 2 = (C * G) ^ 2 from by ring, Real.sqrt_sq (mul_nonneg hC0 hG0)]
  have hGR : G ≤ R := hjet
  calc C * G ≤ C * R := mul_le_mul_of_nonneg_left hGR hC0
    _ ≤ C * (1 + R) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0; linarith

end HilbertFirstDerivativeEnvelope

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem covGrad_gInvDiffSlotCoeff_eq_covGrad_slotInsertEndoCc
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁) =
      covGrad (I := I) (M := M) g₀ 2 2
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1 (gInvDiffRaisedEndoField (I := I) g₀ g₁)) := by
  rw [gInvDiffSlotCoeff_eq_slotInsertEndoCc (I := I) g₀ g₁]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_gInvDiffSlotCoeff_toSection_eval
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) D) v =
      Tensor0SSpace.toModel
        ((slotInsertEndoFib (I := I) (M := M) 2 0 x
            ((endoCovariantDerivative (I := I) (M := M) g₀)
              (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (v 0))) D)
        (Matrix.vecTail v) := by
  rw [covGrad_gInvDiffSlotCoeff_eq_covGrad_slotInsertEndoCc (I := I) g₀ g₁]
  exact covGrad_slotInsertEndoCc_toSection_eq (I := I) (M := M) g₀ 1
    (gInvDiffRaisedEndoField (I := I) g₀ g₁) x D v

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem covGrad_gInvDiffSlotCoeff_endoCov_apply
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x) =
      - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (metricComparisonEndo (I := I) g₀ g₁ x (Y x)) v
      + inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (Y x))).comp
                ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)).toLinearMap) :=
  endoCov_gInvDiffRaisedField_apply (I := I) (M := M) g₀ g₁ Y x v

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SOne_apply_add_comp (x : M) (om : Tensor0SSpace 1 I x)
    (a b : TangentSpace I x) :
    om (fun _ : Fin 1 => a + b) = om (fun _ : Fin 1 => a) + om (fun _ : Fin 1 => b) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hb : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => b) = φ b := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hab : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a + b) = φ (a + b) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ => a + b) = _
  rw [hab, ha, hb, map_add]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SOne_apply_smul_comp (x : M) (om : Tensor0SSpace 1 I x)
    (c : ℝ) (a : TangentSpace I x) :
    om (fun _ : Fin 1 => c • a) = c • om (fun _ : Fin 1 => a) := by
  let φ := continuousMultilinearCurryFin1 ℝ (TangentSpace I x) ℝ
    (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
  have ha : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => a) = φ a := by rw [continuousMultilinearCurryFin1_apply]; rfl
  have hca : (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ : Fin 1 => c • a) = φ (c • a) := by rw [continuousMultilinearCurryFin1_apply]; rfl
  change (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)
      (fun _ => c • a) = _
  rw [hca, ha, map_smul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SOne_apply_neg_comp (x : M) (om : Tensor0SSpace 1 I x)
    (a : TangentSpace I x) :
    om (fun _ : Fin 1 => -a) = -om (fun _ : Fin 1 => a) := by
  have h := tensor0SOne_apply_smul_comp (I := I) x om (-1) a
  simp only [neg_smul, one_smul] at h
  exact h

set_option backward.isDefEq.respectTransparency true in
def connDiffGInvCompositePairing (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun YZ => om (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (metricComparisonEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1))
      map_update_add' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i Y Y'
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              ContinuousLinearMap.add_apply, map_add]
            rw [tensor0SOne_apply_add_comp (I := I) x om]
      map_update_smul' := by
        have hne10 : (1 : Fin 2) ≠ 0 := by decide
        have hne01 : (0 : Fin 2) ≠ 1 := by decide
        intro _ YZ i c Y
        fin_cases i <;>
          · simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, Function.update_self,
              Function.update_of_ne, ne_eq, hne10, hne01, not_false_eq_true,
              ContinuousLinearMap.smul_apply, map_smul]
            rw [tensor0SOne_apply_smul_comp (I := I) x om]
      cont := by
        have hpair : Continuous (fun YZ : Fin 2 → TangentSpace I x => (YZ 0, YZ 1)) :=
          (continuous_apply 0).prodMk (continuous_apply 1)
        have hRaised : Continuous (metricComparisonEndo (I := I) g₀ g₁ x) :=
          (metricComparisonEndo (I := I) g₀ g₁ x).continuous
        have hbil : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
            PDE.DeTurck.connDiff (I := I) g₁ g₀ x
              (metricComparisonEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1)) := by
          have hc : Continuous (fun p : TangentSpace I x × TangentSpace I x =>
              PDE.DeTurck.connDiff (I := I) g₁ g₀ x p.1 p.2) :=
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).continuous₂
          have hcomp : Continuous (fun YZ : Fin 2 → TangentSpace I x =>
              (metricComparisonEndo (I := I) g₀ g₁ x (YZ 0), YZ 1)) :=
            (hRaised.comp (continuous_apply 0)).prodMk (continuous_apply 1)
          exact hc.comp hcomp
        exact ((ContinuousMultilinearMap.coe_continuous
          (om : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => TangentSpace I x) ℝ)).comp
          (continuous_pi (fun _ => hbil))) } : Tensor0SSpace 2 I x)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma gInvCompPairing_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    (connDiffGInvCompositePairing (I := I) g₀ g₁ x om) YZ =
      om (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (metricComparisonEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1)) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma gInvCompPairing_add (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om om' : Tensor0SSpace 1 I x) :
    connDiffGInvCompositePairing (I := I) g₀ g₁ x (om + om') =
      connDiffGInvCompositePairing (I := I) g₀ g₁ x om + connDiffGInvCompositePairing (I := I) g₀ g₁ x om' := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.add_apply om om' _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma gInvCompPairing_smul (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (c : ℝ) (om : Tensor0SSpace 1 I x) :
    connDiffGInvCompositePairing (I := I) g₀ g₁ x (c • om) =
      c • connDiffGInvCompositePairing (I := I) g₀ g₁ x om := by
  apply ContinuousMultilinearMap.ext
  intro YZ
  exact ContinuousMultilinearMap.smul_apply om c _

def connDiffGInvCompositeFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TensorRSSpace 1 2 I x :=
  TensorRSSpace.ofCLM
    (LinearMap.toContinuousLinearMap
      { toFun := fun om => connDiffGInvCompositePairing (I := I) g₀ g₁ x om
        map_add' := gInvCompPairing_add (I := I) g₀ g₁ x
        map_smul' := gInvCompPairing_smul (I := I) g₀ g₁ x })

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma connDiffGInvCompositeFib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        connDiffGInvCompositeFib (I := I) g₀ g₁ x) om =
      connDiffGInvCompositePairing (I := I) g₀ g₁ x om := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem gInvRaisedEndo_section_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
        (metricComparisonEndo (I := I) g₀ g₁ b (Y b))) := by
  refine (inverseMetricSharpFib_g0FlatY_contMDiff (I := I) g₀ g₁ Y).congr (fun b => ?_)
  rw [gInvRaisedEndo_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem connDiffGInvCompositeFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 1 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 1 2 ℝ E)
        (E := fun z : M => TensorRSSpace 1 2 I z) x
        (connDiffGInvCompositeFib (I := I) g₀ g₁ x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun x : M => Tensor0SSpace 2 I x)
    (φ := fun x : M => (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      connDiffGInvCompositeFib (I := I) g₀ g₁ x))
  intro om
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  have hsec : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (connDiffGInvCompositePairing (I := I) g₀ g₁ x (om x))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (connDiffGInvCompositePairing (I := I) g₀ g₁ x (om x) :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
    intro σ x₀
    set b := Module.finBasis ℝ E with hb
    set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
    have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
    have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
    obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
    have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (((PDE.DeTurck.connDiff (I := I) g₁ g₀ x)
            (metricComparisonEndo (I := I) g₀ g₁ x (Y (σ 0) x))) (Y (σ 1) x))) :=
      PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀
        (gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ (Y (σ 0))) (Y (σ 1)).contMDiff
    have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (om x)
          (fun _ : Fin 1 => ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x)
            (metricComparisonEndo (I := I) g₀ g₁ x (Y (σ 0) x))) (Y (σ 1) x))) x₀ :=
      TensorMultilinear.contMDiffAt_section_apply (n := 1) (x₀ := x₀)
        (fun x : M => om x) (om.contMDiff x₀)
        (fun _ : Fin 1 => fun x : M => ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x)
          (metricComparisonEndo (I := I) g₀ g₁ x (Y (σ 0) x))) (Y (σ 1) x))
        (fun _ => (hconn x₀))
    refine hscalar.congr_of_eventuallyEq ?_
    have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
    filter_upwards [h_base₁, hY] with x hx₁ hYx
    rw [continuousMultilinearMap_basis_repr]
    have hframe0 : e₁.symmL ℝ x (b (σ 0)) = (Y (σ 0)) x := by
      rw [hYx (σ 0), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    have hframe1 : e₁.symmL ℝ x (b (σ 1)) = (Y (σ 1)) x := by
      rw [hYx (σ 1), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
      simp [Trivialization.basisAt]
    change (connDiffGInvCompositePairing (I := I) g₀ g₁ x (om x))
        (fun j : Fin 2 => e₁.symmL ℝ x (b (σ j))) = _
    rw [gInvCompPairing_apply]
    rw [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    rw [hframe0, hframe1]
    rfl
  refine hsec.congr ?_
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
def connDiffGInvComposite (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M => connDiffGInvCompositeFib (I := I) g₀ g₁ x
      contMDiff_toFun := connDiffGInvCompositeFib_contMDiff (I := I) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma connDiffGInvComposite_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connDiffGInvComposite (I := I) g₀ g₁).toSection x =
      connDiffGInvCompositeFib (I := I) g₀ g₁ x := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma connDiffGInvComposite_pairing_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (YZ : Fin 2 → TangentSpace I x) :
    ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffGInvComposite (I := I) g₀ g₁).toSection x) om) YZ =
      om (fun _ : Fin 1 =>
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (metricComparisonEndo (I := I) g₀ g₁ x (YZ 0)) (YZ 1)) := by
  rw [connDiffGInvComposite_toSection, connDiffGInvCompositeFib_apply, gInvCompPairing_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem covGrad_gInvDiffSlotCoeff_eq_appCcRS_composite
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x)
    (om : Tensor0SSpace 1 I x) :
    om (fun _ : Fin 1 =>
        ((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v) (Y x)) =
      - ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (connDiffGInvComposite (I := I) g₀ g₁).toSection x) om)
            (fun j : Fin 2 => if j = 0 then Y x else v)
      + om (fun _ : Fin 1 =>
          inverseMetricSharpFib (I := I) g₁ x
            (dualToCotangent (I := I)
              (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (Y x))).comp
                  ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v)).toLinearMap)) := by
  rw [covGrad_gInvDiffSlotCoeff_endoCov_apply (I := I) g₀ g₁ Y x v]
  rw [tensor0SOne_apply_add_comp (I := I) x om,
    tensor0SOne_apply_neg_comp (I := I) x om]
  rw [connDiffGInvComposite_pairing_apply (I := I) g₀ g₁ x om
    (fun j : Fin 2 => if j = 0 then Y x else v)]
  simp only [Fin.isValue, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]

open TensorMultilinear

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem endoCov_gInvDiffRaisedField_fibrewise
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v0) w =
      - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (metricComparisonEndo (I := I) g₀ g₁ x w) v0
      + inverseMetricSharpFib (I := I) g₁ x
          (dualToCotangent (I := I)
            (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
                ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0)).toLinearMap) := by
  classical
  obtain ⟨Y, hYx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x w
  have hk := covGrad_gInvDiffSlotCoeff_endoCov_apply (I := I) (M := M) g₀ g₁ Y x v0
  rw [hYx] at hk
  exact hk

def connArmEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  -(((ContinuousLinearMap.compL ℝ (TangentSpace I x) (TangentSpace I x) (TangentSpace I x)).flip
      (metricComparisonEndo (I := I) g₀ g₁ x)).comp
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma connArmEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    connArmEndo (I := I) g₀ g₁ x v0 w =
      - PDE.DeTurck.connDiff (I := I) g₁ g₀ x (metricComparisonEndo (I := I) g₀ g₁ x w) v0 := by
  rw [connArmEndo, ContinuousLinearMap.neg_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]

def sharpArmEndo (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  (endoCovariantDerivative (I := I) (M := M) g₀)
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) x
    - connArmEndo (I := I) g₀ g₁ x

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma sharpArmEndo_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 w : TangentSpace I x) :
    sharpArmEndo (I := I) g₀ g₁ x v0 w =
      inverseMetricSharpFib (I := I) g₁ x
        (dualToCotangent (I := I)
          (-(cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x w)).comp
              ((PDE.DeTurck.connDiff (I := I) g₁ g₀ x).flip v0)).toLinearMap) := by
  rw [sharpArmEndo, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    connArmEndo_apply, endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x v0 w]
  abel

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma endoCov_eq_connArm_add_sharpArm (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 : TangentSpace I x) :
    (endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x v0 =
      connArmEndo (I := I) g₀ g₁ x v0 + sharpArmEndo (I := I) g₀ g₁ x v0 := by
  apply ContinuousLinearMap.ext; intro w
  rw [ContinuousLinearMap.add_apply, connArmEndo_apply, sharpArmEndo_apply,
    endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x v0 w]

set_option backward.isDefEq.respectTransparency false in
omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem leviCivitaSection_contMDiff_aux (g : SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x}
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M =>
        (⟨x, (LeviCivita (I := I) g).toFun σ x⟩ :
          TotalSpace (E →L[ℝ] E) (fun x : M =>
            TangentSpace I x →L[ℝ] TangentSpace I x))) := by
  have hσ' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) Set.univ := by
    have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ (∞ : WithTop ℕ∞) := by rw [ENat.coe_top_add_one]
    exact (hσ.of_le h_le).contMDiffOn
  rw [← contMDiffOn_univ]
  exact LeviCivita_section_contMDiffOn_univ (I := I) g hσ'

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem connArmEndo_inner_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (connArmEndo (I := I) g₀ g₁ x (V0 x) (W x))) := by
  have hconn : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (metricComparisonEndo (I := I) g₀ g₁ x (W x)) (V0 x))) :=
    PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀
      (gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ W) V0.contMDiff
  refine (hconn.neg_section).congr (fun x => ?_)
  rw [connArmEndo_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem sharpArmEndo_inner_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (sharpArmEndo (I := I) g₀ g₁ x (V0 x) (W x))) := by
  have hendo : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        ((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V0 x) (W x))) := by
    have hΛcovW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((LeviCivita (I := I) g₀).toFun
            (fun y : M => (gInvDiffRaisedEndoField (I := I) g₀ g₁ y) (W y)) x (V0 x))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (leviCivitaSection_contMDiff_aux (I := I) g₀
          (endoApplySection_contMDiff (I := I) (M := M) (gInvDiffRaisedEndoField (I := I) g₀ g₁) W))
        V0.contMDiff
    have hcovWsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((LeviCivita (I := I) g₀).toFun (fun y : M => W y) x (V0 x))) :=
      ContMDiff.clm_bundle_apply (b := id)
        (leviCivitaSection_contMDiff_aux (I := I) g₀ W.contMDiff) V0.contMDiff
    have hcovW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          ((gInvDiffRaisedEndoField (I := I) g₀ g₁ x)
            ((LeviCivita (I := I) g₀).toFun (fun y : M => W y) x (V0 x)))) :=
      endoApplySection_contMDiff (I := I) (M := M) (gInvDiffRaisedEndoField (I := I) g₀ g₁)
        ⟨_, hcovWsec⟩
    refine (hΛcovW.sub_section hcovW).congr (fun x => ?_)
    rw [endoCovariantDerivative_apply (I := I) (M := M) g₀
      (gInvDiffRaisedEndoField (I := I) g₀ g₁) W x (V0 x)]
    rfl
  refine (hendo.sub_section (connArmEndo_inner_contMDiff (I := I) g₀ g₁ V0 W)).congr (fun x => ?_)
  rw [show sharpArmEndo (I := I) g₀ g₁ x (V0 x) (W x) =
      (endoCovariantDerivative (I := I) (M := M) g₀)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V0 x) (W x)
      - connArmEndo (I := I) g₀ g₁ x (V0 x) (W x) from by
    rw [sharpArmEndo, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]]
  rfl

set_option backward.isDefEq.respectTransparency false in
def connArmCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 3 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x (connArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 1 (fun x : M => connArmEndo (I := I) g₀ g₁ x)
          (connArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
def sharpArmCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 3 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x (sharpArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 1 (fun x : M => sharpArmEndo (I := I) g₀ g₁ x)
          (sharpArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma connArmCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connArmCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x (connArmEndo (I := I) g₀ g₁ x)) := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma sharpArmCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpArmCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x (sharpArmEndo (I := I) g₀ g₁ x)) := rfl

set_option backward.isDefEq.respectTransparency false in
def connArmEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x (connArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 0 (fun x : M => connArmEndo (I := I) g₀ g₁ x)
          (connArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
def sharpArmEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 1 2 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x (sharpArmEndo (I := I) g₀ g₁ x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) 0 (fun x : M => sharpArmEndo (I := I) g₀ g₁ x)
          (sharpArmEndo_inner_contMDiff (I := I) g₀ g₁) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma connArmEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (connArmEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x (connArmEndo (I := I) g₀ g₁ x)) := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] lemma sharpArmEndoCc_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (sharpArmEndoCc (I := I) g₀ g₁).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 0 x (sharpArmEndo (I := I) g₀ g₁ x)) := rfl

def bilinEndoCovariantDerivative (g : SmoothRiemannianMetric I M) :
    CovariantDerivative I (E →L[ℝ] (E →L[ℝ] E))
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  HomConnectionGen.homBundleCovariantDerivativeGen I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g)

instance bilinEndoCovariantDerivative_contMDiff (g : SmoothRiemannianMetric I M) :
    (bilinEndoCovariantDerivative (I := I) (M := M) g).ContMDiffCovariantDerivative ∞ :=
  HomConnectionGen.homBundleCovariantDerivativeGen_contMDiff I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem bilinEndoCovariantDerivative_apply (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (Y : ContMDiffSection I E ∞ (TangentSpace I)) (x : M) (v : E) :
    ((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x v) (Y x) =
      (endoCovariantDerivative (I := I) (M := M) g) (fun y => (Arm y) (Y y)) x v -
        (Arm x) ((LeviCivita (I := I) g) (fun y => Y y) x v) :=
  HomConnectionGen.homBundleCovariantDerivativeGen_apply I M
    E (fun x : M => TangentSpace I x)
    (E →L[ℝ] E) (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (LeviCivita (I := I) g) (endoCovariantDerivative (I := I) (M := M) g) Arm Y x v

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem armField_inner_contMDiff
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
        (Arm x (V0 x) (W x))) := by
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) x
        (Arm x (V0 x))) :=
    ContMDiff.clm_bundle_apply (b := id) Arm.contMDiff V0.contMDiff
  exact ContMDiff.clm_bundle_apply (b := id) h1 W.contMDiff

set_option backward.isDefEq.respectTransparency false in
def armSlotEndoCc (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    SmoothCcTensor g (s + 1) (s + 1 + 1) where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x))
      contMDiff_toFun :=
        armSlotFib_contMDiff (I := I) (M := M) s (fun x : M => Arm x)
          (fun V0 W => armField_inner_contMDiff (I := I) (M := M) Arm V0 W) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma armSlotEndoCc_toSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) :
    (armSlotEndoCc (I := I) (M := M) g s Arm).toSection x =
      TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x)) := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem bilinEndoField_contMDiff
    (Arm : Π x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (harm : ∀ (V0 W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x
          (Arm x (V0 x) (W x)))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] E))) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E))
        (E := fun z : M => TangentSpace I z →L[ℝ] (TangentSpace I z →L[ℝ] TangentSpace I z)) x
        (Arm x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E →L[ℝ] E) (V₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (φ := fun x : M => (show TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) from
      Arm x))
  intro V0
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun x : M => TangentSpace I x)
    (F₂ := E) (V₂ := fun x : M => TangentSpace I x)
    (φ := fun x : M => (show TangentSpace I x →L[ℝ] TangentSpace I x from Arm x (V0 x)))
  intro W
  exact harm V0 W

def connArmEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => connArmEndo (I := I) g₀ g₁ x,
    bilinEndoField_contMDiff (I := I) (M := M) (fun x : M => connArmEndo (I := I) g₀ g₁ x)
      (connArmEndo_inner_contMDiff (I := I) g₀ g₁)⟩

def sharpArmEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => sharpArmEndo (I := I) g₀ g₁ x,
    bilinEndoField_contMDiff (I := I) (M := M) (fun x : M => sharpArmEndo (I := I) g₀ g₁ x)
      (sharpArmEndo_inner_contMDiff (I := I) g₀ g₁)⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
@[simp] lemma connArmEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    connArmEndoField (I := I) g₀ g₁ x = connArmEndo (I := I) g₀ g₁ x := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [SigmaCompactSpace M] in
@[simp] lemma sharpArmEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    sharpArmEndoField (I := I) g₀ g₁ x = sharpArmEndo (I := I) g₀ g₁ x := rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma connArmCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    connArmCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 1 (connArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connArmCc_toSection, armSlotEndoCc_toSection, connArmEndoField_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma sharpArmCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpArmCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 1 (sharpArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [sharpArmCc_toSection, armSlotEndoCc_toSection, sharpArmEndoField_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma connArmEndoCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    connArmEndoCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 0 (connArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [connArmEndoCc_toSection, armSlotEndoCc_toSection, connArmEndoField_apply]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma sharpArmEndoCc_eq_armSlotEndoCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpArmEndoCc (I := I) g₀ g₁ = armSlotEndoCc (I := I) (M := M) g₀ 0 (sharpArmEndoField (I := I) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [sharpArmEndoCc_toSection, armSlotEndoCc_toSection, sharpArmEndoField_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma curry_armSlotFib_eq_slotInsert (s : ℕ) (x : M)
    (Arm : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))
    (A : Tensor0SSpace (s + 1) I x) (v0 : TangentSpace I x) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        (bilinearSlotInsertCLM (I := I) (M := M) s x Arm A)) v0 =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x (Arm v0) A := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun vt => ?_)
  rw [tensor0S_curry_apply_eval, armSlotFib_apply_eval]
  simp only [Fin.cons_zero]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma slotInsertEndoFib_sub_left (s : ℕ) (k : Fin s) (x : M)
    (Λ₁ Λ₂ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndoFib (I := I) (M := M) s k x (Λ₁ - Λ₂) =
      slotInsertEndoFib (I := I) (M := M) s k x Λ₁ -
        slotInsertEndoFib (I := I) (M := M) s k x Λ₂ := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [show (-Λ₂ : TangentSpace I x →L[ℝ] TangentSpace I x) = ((-1 : ℝ)) • Λ₂ from by
    rw [neg_one_smul]]
  rw [slotInsertEndoFib_add_left (I := I) (M := M) s k x Λ₁ ((-1 : ℝ) • Λ₂)]
  rw [slotInsertEndoFib_smul_left (I := I) (M := M) s k x (-1 : ℝ) Λ₂]
  rw [neg_one_smul]

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 4000000 in
omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorCovDerivAt_armSlotEndoCc_curry_eq_slotInsertEndoFib (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (v : E) (D : Tensor0SSpace (s + 1) I x) (v0 : E) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (armSlotEndoCc (I := I) (M := M) g s Arm) x v) D)) v0 =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
        (((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x v) v0) D := by
  classical
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel (s + 1) ℝ E) (V := fun y : M => Tensor0SSpace (s + 1) I y)
    (n := (⊤ : ℕ∞)) x D
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x v0
  set ASA := armSlotEndoCc (I := I) (M := M) g s Arm with hASA
  have hlamY : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z) y ((Arm y) (Y y))) :=
    ContMDiff.clm_bundle_apply (b := id) Arm.contMDiff Y.contMDiff
  let lamY : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) :=
    ⟨fun y : M => (Arm y) (Y y), hlamY⟩
  set SIΛ := endoSlotZeroCcTensor (I := I) (M := M) g s lamY with hSIΛ
  have hbridge_app : ∀ y : M, ∀ A : Tensor0SSpace (s + 1) I y,
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) y
          ((show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1 + 1) I y from
            ASA.toSection y) A)) (Y y) =
        (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SIΛ.toSection y) A := by
    intro y A
    rw [hASA, armSlotEndoCc_toSection]
    rw [show (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1 + 1) I y from
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s y (Arm y))) A =
          bilinearSlotInsertCLM (I := I) (M := M) s y (Arm y) A from rfl]
    rw [curry_armSlotFib_eq_slotInsert (I := I) (M := M) s y (Arm y) A (Y y)]
    rw [hSIΛ, slotInsertEndoCc_toSection]
    rfl
  have hw_at_full : TensorSectionMDiffAt (I := I) (s + 1 + 1)
      (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1 + 1) I y from
        ASA.toSection y) (w y)) x := by
    have hsm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1 + 1) ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1 + 1) ℝ E)
          (E := fun z : M => Tensor0SSpace (s + 1 + 1) I z) y
          ((show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1 + 1) I y from
            ASA.toSection y) (w y))) :=
      ContMDiff.clm_bundle_apply (b := id) ASA.toSection.contMDiff w.contMDiff
    exact (hsm x).mdifferentiableAt (by norm_num)
  have hSIw_at : TensorSectionMDiffAt (I := I) (s + 1)
      (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
        SIΛ.toSection y) (w y)) x := by
    have hsm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
          (E := fun z : M => Tensor0SSpace (s + 1) I z) y
          ((show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SIΛ.toSection y) (w y))) :=
      ContMDiff.clm_bundle_apply (b := id) SIΛ.toSection.contMDiff w.contMDiff
    exact (hsm x).mdifferentiableAt (by norm_num)
  have hCL_U := tensor0SCovariantDerivative_curriedSection_hom_leibniz (I := I) (M := M) g (s + 1)
    (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1 + 1) I y from
      ASA.toSection y) (w y)) (x := x) hw_at_full Y v
  have hbridge_fun : (fun y : M => Tensor0SNabla.curriedSection I M
        (fun z : M => (show Tensor0SSpace (s + 1) I z →L[ℝ] Tensor0SSpace (s + 1 + 1) I z from
          ASA.toSection z) (w z)) y (Y y)) =
      (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
        SIΛ.toSection y) (w y)) := by
    funext y
    rw [Tensor0SNabla.curriedSection_apply]
    exact hbridge_app y (w y)
  have hHL_ASA := tensorRSCovariantDerivative_apply (I := I) (M := M) (s + 1) (s + 1 + 1)
    (LeviCivita (I := I) g) ASA.toSection w x v
  have hHL_SI := tensorRSCovariantDerivative_apply (I := I) (M := M) (s + 1) (s + 1)
    (LeviCivita (I := I) g) SIΛ.toSection w x v
  have hbilin := bilinEndoCovariantDerivative_apply (I := I) (M := M) g Arm Y x v
  have hEndoSI := tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g s lamY x v
  set Lw : Tensor0SSpace (s + 1) I x :=
    Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) (fun y : M => w y) x v with hLw
  set Lw' : Tensor0SSpace (s + 1) I x :=
    Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g) w x v with hLw'
  have hLwLw' : Lw = Lw' := rfl
  set NY : TangentSpace I x := (LeviCivita (I := I) g).toFun (fun y => Y y) x v with hNY
  have hCURVE : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1) ASA x v) (w x))) (Y x) =
      slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
          ((endoCovariantDerivative (I := I) (M := M) g) lamY x v) (w x)
        - slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) NY) (w x) := by
    have hcurryDeriv : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
          ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
            tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1) ASA x v) (w x)) =
        tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
            (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1 + 1) (LeviCivita (I := I) g)
              (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1 + 1) I y from
                ASA.toSection y) (w y)) x v)
          - tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
              ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
                ASA.toSection x) Lw') := by
      rw [tensorCovDerivAt_def (I := I) (M := M) g (s + 1) (s + 1 + 1) ASA x v]
      rw [show (⇑w : ∀ z : M, Tensor0SSpace (s + 1) I z) = (fun z : M => w z) from rfl] at hHL_ASA
      rw [hHL_ASA, map_sub]
    rw [hcurryDeriv]
    rw [ContinuousLinearMap.sub_apply]
    rw [eq_sub_of_add_eq hCL_U.symm]
    rw [show (⇑w : ∀ z : M, Tensor0SSpace (s + 1) I z) = (fun z : M => w z) from rfl]
    rw [hbridge_fun]
    have hcurrASA_NY : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
          ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
            ASA.toSection x) (w x))) NY =
        slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) NY) (w x) := by
      rw [hASA, armSlotEndoCc_toSection]
      rw [show (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x))) (w x) =
            bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x) (w x) from rfl]
      rw [curry_armSlotFib_eq_slotInsert (I := I) (M := M) s x (Arm x) (w x) NY]
    have hSIderiv : Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g)
          (fun y : M => (show Tensor0SSpace (s + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
            SIΛ.toSection y) (w y)) x v =
        (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1) SIΛ x v) (w x) +
          (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from SIΛ.toSection x) Lw' := by
      rw [tensorCovDerivAt_def (I := I) (M := M) g (s + 1) (s + 1) SIΛ x v]
      rw [show (⇑w : ∀ z : M, Tensor0SSpace (s + 1) I z) = (fun z : M => w z) from rfl] at hHL_SI
      rw [eq_sub_iff_add_eq] at hHL_SI
      rw [← hHL_SI]
    rw [hSIderiv, hEndoSI]
    have hSIw : (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from SIΛ.toSection x) Lw' =
        slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) (Y x)) Lw' := by
      rw [hSIΛ, slotInsertEndoCc_toSection]
      rfl
    have hcurrW_NY : Tensor0SNabla.curriedSection I M
          (fun z : M => (show Tensor0SSpace (s + 1) I z →L[ℝ] Tensor0SSpace (s + 1 + 1) I z from
            ASA.toSection z) (w z)) x NY =
        slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) NY) (w x) := by
      rw [Tensor0SNabla.curriedSection_apply]
      exact hcurrASA_NY
    have hcurrASA_Lw : (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x
          ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
            ASA.toSection x) Lw')) (Y x) =
        slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) (Y x)) Lw' := by
      rw [hASA, armSlotEndoCc_toSection]
      rw [show (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
          TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x))) Lw' =
            bilinearSlotInsertCLM (I := I) (M := M) s x (Arm x) Lw' from rfl]
      rw [curry_armSlotFib_eq_slotInsert (I := I) (M := M) s x (Arm x) Lw' (Y x)]
    rw [hSIw, hcurrW_NY, hcurrASA_Lw]
    abel
  rw [← hw, ← hY]
  rw [hCURVE]
  rw [← ContinuousLinearMap.sub_apply
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
      ((endoCovariantDerivative (I := I) (M := M) g) lamY x v))
    (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x ((Arm x) NY)) (w x)]
  rw [← slotInsertEndoFib_sub_left (I := I) (M := M) (s + 1) 0 x
    ((endoCovariantDerivative (I := I) (M := M) g) lamY x v) ((Arm x) NY)]
  congr 1
  rw [hbilin]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivAt_armSlotEndoCc_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (v : E) :
    (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
          (armSlotEndoCc (I := I) (M := M) g s Arm) x v) =
      bilinearSlotInsertCLM (I := I) (M := M) s x
        ((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x v) := by
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from (Fin.cons_self_tail m).symm]
  rw [armSlotFib_apply_eval]
  rw [← tensor0S_curry_apply_eval (I := I) (M := M) (n := s + 1)
    (T := (show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
      tensorCovDerivAt (I := I) (M := M) g (s + 1) (s + 1 + 1)
        (armSlotEndoCc (I := I) (M := M) g s Arm) x v) D) (v0 := m 0) (vs := Matrix.vecTail m)]
  rw [tensorCovDerivAt_armSlotEndoCc_curry_eq_slotInsertEndoFib (I := I) (M := M) g s Arm x v D (m 0)]
  simp only [Fin.cons_zero]
  rw [show Matrix.vecTail (Fin.cons (m 0) (Matrix.vecTail m)) = Matrix.vecTail m from by
    funext k; rfl]

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_armSlotEndoCc_toSection_eq (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) (D : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1 + 1 + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1 + 1) I x from
          (covGrad (I := I) (M := M) g (s + 1) (s + 1 + 1)
            (armSlotEndoCc (I := I) (M := M) g s Arm)).toSection x) D) v =
      Tensor0SSpace.toModel
        ((bilinearSlotInsertCLM (I := I) (M := M) s x
            ((bilinEndoCovariantDerivative (I := I) (M := M) g) Arm x (v 0))) D)
        (Matrix.vecTail v) := by
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g (s + 1) (s + 1 + 1)
    (armSlotEndoCc (I := I) (M := M) g s Arm) x D v]
  rw [tensorCovDerivAt_armSlotEndoCc_eq (I := I) (M := M) g s Arm x (v 0)]

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_gInvDiffSlotCoeff_eq_slotInsert_section
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 2 2 (gInvDiffSlotCoeff (I := I) g₀ g₁) =
      connArmCc (I := I) g₀ g₁ + sharpArmCc (I := I) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext
  intro D
  apply Tensor0SSpace.toModel_injective (I := I) (M := M)
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((connArmCc (I := I) g₀ g₁ + sharpArmCc (I := I) g₀ g₁).toSection x) =
      (connArmCc (I := I) g₀ g₁).toSection x + (sharpArmCc (I := I) g₀ g₁).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
      ((connArmCc (I := I) g₀ g₁).toSection x + (sharpArmCc (I := I) g₀ g₁).toSection x)) D) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (connArmCc (I := I) g₀ g₁).toSection x) D +
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (sharpArmCc (I := I) g₀ g₁).toSection x) D from rfl]
  change Tensor0SSpace.toModel _ v = Tensor0SSpace.toModel (_ + _) v
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [covGrad_gInvDiffSlotCoeff_toSection_eval (I := I) (M := M) g₀ g₁ x D v]
  rw [connArmCc_toSection, sharpArmCc_toSection]
  change _ = Tensor0SSpace.toModel
      (bilinearSlotInsertCLM (I := I) (M := M) 1 x (connArmEndo (I := I) g₀ g₁ x) D) v +
    Tensor0SSpace.toModel
      (bilinearSlotInsertCLM (I := I) (M := M) 1 x (sharpArmEndo (I := I) g₀ g₁ x) D) v
  rw [armSlotFib_apply_eval, armSlotFib_apply_eval]
  rw [endoCov_eq_connArm_add_sharpArm (I := I) g₀ g₁ x (v 0)]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply,
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

omit [NeZero (Module.finrank ℝ E)] in
theorem rfns_iteratedCovGrad_gInvDiffSlotCoeff_succ_le_arms
    (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 2 2 (m + 1) (gInvDiffSlotCoeff (I := I) g₀ g₁)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 ((2 + 1) + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m (connArmCc (I := I) g₀ g₁)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 ((2 + 1) + m) x
            ((iteratedCovGrad (I := I) g₀ 2 3 m (sharpArmCc (I := I) g₀ g₁)).toSection x) := by
  rw [← rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 2 2 m
    (gInvDiffSlotCoeff (I := I) g₀ g₁) x]
  rw [covGrad_gInvDiffSlotCoeff_eq_slotInsert_section (I := I) g₀ g₁]
  rw [iteratedCovGrad_add]
  exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 ((2 + 1) + m) x _ _

section NormedDomReindexing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem rsDomDomCongrFib_contMDiff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) x
        (tensorRS_domDomCongr σ (R.toSection x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel r ℝ E) (V₁ := fun x : M => Tensor0SSpace r I x)
    (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
    (φ := fun x : M => tensorRS_domDomCongr σ (R.toSection x))
  intro Y
  have hZ := ContMDiff.clm_bundle_apply (b := id) R.toSection.contMDiff Y.contMDiff
  have hperm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SSpace.toModel
              ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))) :
            Tensor0SSpace s I x))).mpr ?_
    have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x))).mp hZ
    intro τ x₀
    refine (hZcoord (τ ∘ σ) x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x))))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  refine hperm.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SSpace s I z) x t) ?_
  apply Tensor0SSpace.toModel_injective
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorRS_domDomCongr σ (R.toSection x)) (Y x))
    = Tensor0SSpace.toModel
        (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))))
  rw [toModel_rsDomDomCongr_apply, Tensor0SSpace.toModel_ofModel]

set_option backward.isDefEq.respectTransparency false in
def rsDomDomCongrSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) : SmoothCcTensor g r s where
  toSection :=
    { toFun := fun x : M => tensorRS_domDomCongr σ (R.toSection x)
      contMDiff_toFun := rsDomDomCongrFib_contMDiff (I := I) (M := M) g r s σ R }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma rsDomDomCongrSection_toSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) (x : M) :
    (rsDomDomCongrSection (I := I) (M := M) g r s σ R).toSection x =
      tensorRS_domDomCongr σ (R.toSection x) := rfl

end NormedDomReindexing

def armSlotEndoPassZeroCc (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    SmoothCcTensor g 2 3 :=
  rsDomDomCongrSection (I := I) (M := M) g 2 3 (finRotate 3)
    (armSlotEndoCc (I := I) (M := M) g 1 Arm)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma armSlotEndoPassZeroCc_toSection (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) :
    (armSlotEndoPassZeroCc (I := I) (M := M) g Arm).toSection x =
      tensorRS_domDomCongr (finRotate 3)
        ((armSlotEndoCc (I := I) (M := M) g 1 Arm).toSection x) := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem toModel_appCcRS_armSlotEndoPassZeroCc_eval (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (W : SmoothCcTensor g 1 2) (x : M) (om : Tensor0SSpace 1 I x)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (ccOperatorFieldComp (I := I) (M := M) g 1 2 3
            (armSlotEndoPassZeroCc (I := I) (M := M) g Arm) W).toSection x) om) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om)
        (fun j : Fin 2 => if j = 0 then Arm x (v 1) (v 2) else v 0) := by
  classical
  have hcomp : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (ccOperatorFieldComp (I := I) (M := M) g 1 2 3
          (armSlotEndoPassZeroCc (I := I) (M := M) g Arm) W).toSection x) om =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (armSlotEndoPassZeroCc (I := I) (M := M) g Arm).toSection x)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om) := by
    rw [appCcRS_toSection]
    rfl
  rw [hcomp, armSlotEndoPassZeroCc_toSection]
  rw [toModel_rsDomDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]
  rw [armSlotEndoCc_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x (Arm x)))
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om) =
      bilinearSlotInsertCLM (I := I) (M := M) 1 x (Arm x)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om) from rfl]
  rw [armSlotFib_apply_eval, slotInsertEndoFib_apply_eval]
  have hr0 : finRotate 3 (0 : Fin 3) = 1 := by decide
  have hr1 : finRotate 3 (1 : Fin 3) = 2 := by decide
  have hr2 : finRotate 3 (2 : Fin 3) = 0 := by decide
  congr 1
  funext j
  refine Fin.cases ?_ ?_ j
  · rw [Function.update_self, if_pos rfl]
    change Arm x (v (finRotate 3 0)) (v (finRotate 3 1)) = Arm x (v 1) (v 2)
    rw [hr0, hr1]
  · intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [Function.update_of_ne (Fin.succ_ne_zero 0), if_neg (Fin.succ_ne_zero 0)]
    change v (finRotate 3 2) = v 0
    rw [hr2]

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_iteratedCovGrad_armSlotEndoPassZeroCc_toSection_eq
    (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (j : ℕ) :
    ∃ τ : Equiv.Perm (Fin (3 + j)), ∀ (x : M) (d : Tensor0SSpace 2 I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
            (iteratedCovGrad (I := I) g 2 3 j
              (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x) d) =
        ContinuousMultilinearMap.domDomCongr τ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
              (iteratedCovGrad (I := I) g 2 3 j
                (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x) d)) := by
  induction j with
  | zero =>
    refine ⟨finRotate 3, fun x d => ?_⟩
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero, armSlotEndoPassZeroCc_toSection,
      toModel_rsDomDomCongr_apply]
  | succ j ih =>
    obtain ⟨τ, hτ⟩ := ih
    refine ⟨Equiv.Perm.decomposeFin.symm (0, τ), fun x d => ?_⟩
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ]
    apply ContinuousMultilinearMap.ext
    intro v
    exact covGrad_rs_toModel_domDomCongr (I := I) (M := M) g 2 (3 + j) τ
      (iteratedCovGrad (I := I) g 2 3 j (armSlotEndoCc (I := I) (M := M) g 1 Arm))
      (iteratedCovGrad (I := I) g 2 3 j (armSlotEndoPassZeroCc (I := I) (M := M) g Arm))
      hτ x d v

theorem riemannianFiberNormSq_iteratedCovGrad_armSlotEndoPassZeroCc_eq
    (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 (3 + j) x
        ((iteratedCovGrad (I := I) g 2 3 j
          (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 2 (3 + j) x
        ((iteratedCovGrad (I := I) g 2 3 j
          (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x) := by
  classical
  obtain ⟨τ, hτ⟩ := exists_iteratedCovGrad_armSlotEndoPassZeroCc_toSection_eq
    (I := I) (M := M) g Arm j
  have hsec : (iteratedCovGrad (I := I) g 2 3 j
        (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x =
      tensorRS_domDomCongr τ
        ((iteratedCovGrad (I := I) g 2 3 j
          (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x) := by
    apply ContinuousLinearMap.ext
    intro d
    apply Tensor0SSpace.toModel_injective
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
          (iteratedCovGrad (I := I) g 2 3 j
            (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x) d) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
          tensorRS_domDomCongr τ
            ((iteratedCovGrad (I := I) g 2 3 j
              (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x)) d)
    rw [toModel_rsDomDomCongr_apply]
    exact hτ x d
  rw [hsec]
  exact riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g 2 (3 + j) x τ _

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metricCovDeriv_symm_right
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : Π b : M, TangentSpace I b) (x : M) :
    metricCovDeriv (I := I) g cov X Y Z x = metricCovDeriv (I := I) g cov X Z Y x := by
  unfold metricCovDeriv
  rw [show (fun b : M => g.inner b (Z b) (Y b)) = (fun b : M => g.inner b (Y b) (Z b)) from by
    funext b; rw [g.symm b (Z b) (Y b)]]
  rw [g.symm x (cov.toFun Y x (X x)) (Z x), g.symm x (Y x) (cov.toFun Z x (X x))]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metricDiffCovDeriv_symm_right
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) :
    metricDiffCovDeriv (I := I) g₁ g₀ X Y Z x =
      metricDiffCovDeriv (I := I) g₁ g₀ X Z Y x := by
  unfold metricDiffCovDeriv
  rw [metricCovDeriv_symm_right (I := I) g₁ (LeviCivita (I := I) g₀) X Y Z x,
    metricCovDeriv_symm_right (I := I) g₀ (LeviCivita (I := I) g₀) X Y Z x]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem endoCovariantDerivative_gInvDiffRaisedEndoField_resolvent
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (V W Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    g₁.inner x
        (((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V x)) (W x)) (Z x) =
      - metricDiffCovDeriv (I := I) g₁ g₀
          (fun y : M => V y)
          (fun y : M => metricComparisonEndo (I := I) g₀ g₁ y (W y))
          (fun y : M => Z y) x := by
  classical
  have hg1gir : ∀ u : TangentSpace I x,
      g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x (W x)) u = g₀.inner x (W x) u := by
    intro u
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_inner, cotangentToDualLinear_apply,
      cotangentToDual_g0FlatCLM]
  have hpair : g₁.inner x
        (((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V x)) (W x)) (Z x) =
      - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (metricComparisonEndo (I := I) g₀ g₁ x (W x)) (V x)) (Z x)
        - g₀.inner x (W x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) := by
    rw [endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x (V x) (W x)]
    rw [map_add, ContinuousLinearMap.add_apply, map_neg, ContinuousLinearMap.neg_apply,
      inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    rw [show (cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (W x)))
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) =
          g₀.inner x (W x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) from
      cotangentToDual_g0FlatCLM (I := I) g₀ x (W x)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x))]
    ring
  have hk1 := connDiff_koszul_metricDiff (I := I) g₁ g₀
    (X := fun y : M => V y) (Y := fun y : M => metricComparisonEndo (I := I) g₀ g₁ y (W y))
    (Z := fun y : M => Z y) V.mdifferentiableAt
    ((gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ W x).mdifferentiableAt (by norm_num))
    Z.mdifferentiableAt
  have hk2 := connDiff_koszul_metricDiff (I := I) g₁ g₀
    (X := fun y : M => V y) (Y := fun y : M => Z y)
    (Z := fun y : M => metricComparisonEndo (I := I) g₀ g₁ y (W y)) V.mdifferentiableAt
    Z.mdifferentiableAt
    ((gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ W x).mdifferentiableAt (by norm_num))
  have hsym := metricDiffCovDeriv_symm_right (I := I) g₁ g₀
    (fun y : M => V y) (fun y : M => Z y)
    (fun y : M => metricComparisonEndo (I := I) g₀ g₁ y (W y)) x
  have hconv : g₀.inner x (W x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x))
        (metricComparisonEndo (I := I) g₀ g₁ x (W x)) := by
    rw [← hg1gir (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)),
      g₁.symm x (metricComparisonEndo (I := I) g₀ g₁ x (W x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x))]
  rw [hpair, hconv]
  simp only [] at hk1 hk2
  linarith [hk1, hk2, hsym]

section NormedReindexingNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem rfns_iteratedCovGrad_rsDomDomCongr_both_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ' : Equiv.Perm (Fin r)) (σ : Equiv.Perm (Fin s))
    (R : SmoothCcTensor g r s) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i
          (reindexCoeffGen (I := I) (M := M) g r s
            (rsDomDomCongrSection (I := I) (M := M) g r s σ R) σ')).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i R).toSection x) := by
  rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g r s
    (rsDomDomCongrSection (I := I) (M := M) g r s σ R) σ' i x]
  exact riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g r s σ R
    (rsDomDomCongrSection (I := I) (M := M) g r s σ R)
    (fun y d => by
      rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotInsertEndoCc_succ_eq_reindex_slotExtend
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1) Λ =
      reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
        (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
          (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)))
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1) Λ).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)))
          (Equiv.swap (0 : Fin (s + 1 + 1)) 1)).toSection x) D) m
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval]
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply, rsDomDomCongrSection_toSection,
    toModel_rsDomDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply, slotExtend_toSection]
  rw [show (fun k : Fin (s + 1 + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) k)) =
      Fin.cons (m 1) (fun j : Fin (s + 1) =>
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ j))) from by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [Fin.cons_zero, Equiv.swap_apply_left]
    · simp only [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval]
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval, tensor0S_curry_apply_eval,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  have hswap_succ0 : (Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (0 : Fin (s + 1))) = 0 := by
    rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl, Equiv.swap_apply_right]
  rw [hswap_succ0]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k₁ => ?_) k
  · rw [Equiv.swap_apply_left,
      show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl, Fin.cons_succ,
      Function.update_self, Function.update_self]
  · refine Fin.cases ?_ (fun k₂ => ?_) k₁
    · have h10 : (1 : Fin (s + 1 + 1)) ≠ 0 := by
        rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact Fin.succ_ne_zero _
      rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl,
        Function.update_of_ne h10, Equiv.swap_apply_right, Fin.cons_zero]
    · have hne0 : (Fin.succ (Fin.succ k₂) : Fin (s + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
      have hne1 : (Fin.succ (Fin.succ k₂) : Fin (s + 1 + 1)) ≠ 1 := by
        rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
      rw [Function.update_of_ne hne0, Equiv.swap_apply_of_ne_of_ne hne0 hne1, Fin.cons_succ,
        Function.update_of_ne (Fin.succ_ne_zero k₂)]
      change m (Fin.succ (Fin.succ k₂)) =
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (Fin.succ k₂)))
      rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]

theorem rfns_iteratedCovGrad_slotInsertEndoCc_le_endo
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 Λ)).toSection x) := by
  induction s with
  | zero =>
    rw [pow_zero, one_mul]
  | succ s ih =>
    have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have hA : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1 + 1) ((s + 1 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ (s + 1 + 1) (s + 1 + 1) i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1) Λ)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1 + 1) ((s + 1 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ (s + 1 + 1) (s + 1 + 1) i
            (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ))).toSection x) := by
      rw [slotInsertEndoCc_succ_eq_reindex_slotExtend (I := I) (M := M) g₀ s Λ]
      exact rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)) i x
    rw [hA]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ (s + 1) (s + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ) i x) ?_
    calc (Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
              ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)).toSection x)
        ≤ (Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) ^ s *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
                ((iteratedCovGrad (I := I) g₀ 1 1 i
                  (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 Λ)).toSection x)) :=
          mul_le_mul_of_nonneg_left ih hfr
      _ = (Module.finrank ℝ E : ℝ) ^ (s + 1) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 1 i
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 Λ)).toSection x) := by
          rw [pow_succ]; ring

end NormedReindexingNorm

end Connection
end Integral
end DifferentialGeometry

end
