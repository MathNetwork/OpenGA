import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapSecondOrderIBP
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenIdentity
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorCovGradL2InnerDirichletBridge
import DifferentialGeometry.Geometry.Connection.DivergenceCovariantTrace
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorRSMetricCompatible
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.TensorRicciCommutator
import DifferentialGeometry.Geometry.Curvature.Bochner.WeitzenbockIdentity
import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Proper
import DifferentialGeometry.Geometry.Operator.MetricSharpSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Tensor.TensorRSRiemannian
open Tensor0SNabla TensorRSNabla TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def dirichletForm
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M) :
    TangentSpace I b →ₗ[ℝ] ℝ where
  toFun X := tensorInnerPointwise (I := I) (M := M) g 0 2 b
    (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g 0 2 T b X))
    (TensorRSSpace.toModel (v.toSection b))
  map_add' X Y := by
    have hcov : tensorCovDerivAt (I := I) (M := M) g 0 2 T b (X + Y) =
        tensorCovDerivAt (I := I) (M := M) g 0 2 T b X +
          tensorCovDerivAt (I := I) (M := M) g 0 2 T b Y := by
      change (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b (X + Y) = _
      rw [ContinuousLinearMap.map_add]
      rfl
    rw [hcov, TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  map_smul' c X := by
    have hcov : tensorCovDerivAt (I := I) (M := M) g 0 2 T b (c • X) =
        c • tensorCovDerivAt (I := I) (M := M) g 0 2 T b X := by
      change (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b (c • X) = _
      rw [ContinuousLinearMap.map_smul]
      rfl
    rw [hcov, TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left]
    rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma dirichletForm_apply
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M)
    (X : TangentSpace I b) :
    dirichletForm (I := I) (M := M) g T v b X =
      tensorInnerPointwise (I := I) (M := M) g 0 2 b
        (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g 0 2 T b X))
        (TensorRSSpace.toModel (v.toSection b)) := rfl

def dirichletVF
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M) :
    TangentSpace I b :=
  metricSharp (I := I) g b (dirichletForm (I := I) (M := M) g T v b)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma inner_dirichletVF
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M)
    (X : TangentSpace I b) :
    g.inner b (dirichletVF (I := I) (M := M) g T v b) X =
      dirichletForm (I := I) (M := M) g T v b X := by
  rw [dirichletVF]
  exact inner_metricSharp (I := I) g b (dirichletForm (I := I) (M := M) g T v b) X

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma dirichletForm_chartBasis_component_contMDiffOn
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => dirichletForm (I := I) (M := M) g T v b
        (chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  have hcov_section : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun y : M => TensorRSSpace 0 2 I y) b
        (tensorCovDerivAt (I := I) (M := M) g 0 2 T b
          (chartBasisVecFiber (I := I) α j b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    tensorCovDeriv_chartBasis_contMDiffOn (I := I) (M := M) g 0 2 T α j
  have hcov_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (0 + 2) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g 0 2 α b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 2 T b
            (chartBasisVecFiber (I := I) α j b))))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose_of_section_contMDiffOn
      (I := I) (M := M) g 0 2
      (fun b : M => tensorCovDerivAt (I := I) (M := M) g 0 2 T b
        (chartBasisVecFiber (I := I) α j b)) α hcov_section
  have hv_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (0 + 2) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g 0 2 α b
        (TensorRSSpace.toModel (v.toSection b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose (I := I) (M := M) g 0 2 v.toSection α
  have hinner : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 2 T b
              (chartBasisVecFiber (I := I) α j b)))
          (TensorRSSpace.toModel (v.toSection b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections
      (I := I) (M := M) g 0 2
      (fun b : M => tensorCovDerivAt (I := I) (M := M) g 0 2 T b
        (chartBasisVecFiber (I := I) α j b))
      (fun b : M => v.toSection b) α hcov_lowered hv_lowered
  have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet =
      (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
      (I := I) α
  rw [hbase_eq] at hinner
  refine hinner.congr ?_
  intro b _
  rw [dirichletForm_apply]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma dirichletVF_contMDiff
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b (dirichletVF (I := I) (M := M) g T v b)) :=
  metricSharp_contMDiff_total (I := I) g
    (cv := fun b : M => dirichletForm (I := I) (M := M) g T v b)
    (fun α j => dirichletForm_chartBasis_component_contMDiffOn
      (I := I) (M := M) g T v α j)

def dirichletVFSection
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ContMDiffSection.mk
    (fun b : M => dirichletVF (I := I) (M := M) g T v b)
    (dirichletVF_contMDiff (I := I) (M := M) g T v)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma dirichletVFSection_apply
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M) :
    dirichletVFSection (I := I) (M := M) g T v b =
      dirichletVF (I := I) (M := M) g T v b := rfl

omit [CompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma divergence_g_chartBasis_metricTrace_self
    (g : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    divergence_g (I := I) g Z b =
      ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g b b m n *
          g.inner b
            ((LeviCivita (I := I) g).toFun Z.toFun b
              (chartBasisVecFiber (I := I) b m b))
            (chartBasisVecFiber (I := I) b n b) := by
  classical
  have hb_src : b ∈ (chartAt H b).source := mem_chart_source H b
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) b := by
    rw [mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) b b]
    exact mem_extChartAt_source (I := I) b
  rw [voss_weyl_divergence_formula (I := I) g b Z hb_src]
  rw [localDivergence_eq_coord_covariant_divergence (I := I) g b Z hb_good]
  rw [metricTrace_eq_coord_covariant_divergence (I := I) g b Z hb_good]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [show (∑ i : Fin (Module.finrank ℝ E),
          chartCoeffOnE (I := I) b Z i (extChartAt I b b) *
            ∑ k : Fin (Module.finrank ℝ E),
              chartChristoffel (I := I) g b i k k (extChartAt I b b)) =
        ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
          chartChristoffel (I := I) g b i k k (extChartAt I b b) *
            chartCoeffOnE (I := I) b Z i (extChartAt I b b) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [chartChristoffel_symm (I := I) g b k i i]

omit [CompactSpace M] in
omit [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
lemma divergence_g_eq_smoothOrthoFrame_trace
    (g : SmoothRiemannianMetric I M)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (b : M) :
    divergence_g (I := I) g Z b =
      ∑ i : Fin (Module.finrank ℝ E),
        g.inner b
          ((LeviCivita (I := I) g).toFun Z.toFun b
            (smoothOrthoFrame (I := I) g b i b))
          (smoothOrthoFrame (I := I) g b i b) := by
  classical
  set L : TangentSpace I b →L[ℝ] TangentSpace I b :=
    (LeviCivita (I := I) g).toFun Z.toFun b with hL_def
  set Hb : TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ :=
    (g.inner b).comp L with hHb_def
  have hHb_apply : ∀ u w : TangentSpace I b, Hb u w = g.inner b (L u) w := by
    intro u w
    rw [hHb_def, ContinuousLinearMap.comp_apply]
  have hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner b (smoothOrthoFrame (I := I) g b i b)
        (smoothOrthoFrame (I := I) g b j b) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j
  have htrace := orthonormal_basis_bilin_trace (I := I) g b Hb
    (fun i : Fin (Module.finrank ℝ E) => smoothOrthoFrame (I := I) g b i b) hB_orth
  rw [divergence_g_chartBasis_metricTrace_self (I := I) g Z b]
  rw [show (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g b b m n *
            g.inner b (L (chartBasisVecFiber (I := I) b m b))
              (chartBasisVecFiber (I := I) b n b)) =
        ∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g b b m n *
            Hb ((chartModelBasis E) m) ((chartModelBasis E) n) from ?_]
  · rw [← htrace]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hHb_apply]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hHb_apply, chartBasisVecFiber_self (I := I) b m,
      chartBasisVecFiber_self (I := I) b n]

omit [CompactSpace M] in
private lemma divergence_dirichletVF_summand_eq
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    g.inner b
        ((LeviCivita (I := I) g).toFun
          (dirichletVFSection (I := I) (M := M) g T v).toFun b
          (smoothOrthoFrame (I := I) g b i b))
        (smoothOrthoFrame (I := I) g b i b) =
      tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (tensorSecondCovDeriv (I := I) g 0 2
              (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
              (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 2 T b
              (smoothOrthoFrame (I := I) g b i b)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 2 v b
              (smoothOrthoFrame (I := I) g b i b))) := by
  classical
  set B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun y : M => smoothOrthoFrame (I := I) g b i y,
      smoothOrthoFrame_smooth (I := I) g b i⟩ with hB_def
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    dirichletVFSection (I := I) (M := M) g T v with hZ_def
  have hBb : (B : ∀ y, TangentSpace I y) b = smoothOrthoFrame (I := I) g b i b := rfl
  have hleib := leibniz_inner (I := I) g
    (V := fun y : M => Z y) (W := fun y : M => B y)
    Z.contMDiff B.contMDiff
    (x := b) ((B : ∀ y, TangentSpace I y) b)
  have hfun : (fun y : M => g.inner y (Z y) (B y)) =
      tensorInnerScalar (I := I) (M := M) g 0 2
        (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection := by
    funext y
    rw [hZ_def, dirichletVFSection_apply, inner_dirichletVF, dirichletForm_apply,
      tensorInnerScalar_apply, covDerivAlongVFSection_apply]
    rfl
  have hprod : tangentSectionAction (I := I) B
        (fun y : M => g.inner y (Z y) (B y)) b =
      tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (covDerivAlongVFSection (I := I) (M := M) g
              (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) B b))
          (TensorRSSpace.toModel (v.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (covDerivAlongVFSection (I := I) (M := M) g T.toSection B b))
          (TensorRSSpace.toModel
            (covDerivAlongVFSection (I := I) (M := M) g v.toSection B b)) := by
    rw [show tangentSectionAction (I := I) B
            (fun y : M => g.inner y (Z y) (B y)) =
          tangentSectionAction (I := I) B
            (tensorInnerScalar (I := I) (M := M) g 0 2
              (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection) from by
      rw [hfun]]
    rw [tangentSectionAction_tensorInnerScalar (I := I) (M := M) g 0 2
      (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) v.toSection B b]
    congr 1
    · rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 2
        (covDerivAlongVFSection (I := I) (M := M) g
          (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) B)
        v.toSection b]
      rw [toModel_liftedTensorSection_covDerivAlongVFSection (I := I) (M := M) g
        (covDerivAlongVFSection (I := I) (M := M) g T.toSection B) B b]
    · rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g 0 2
        (covDerivAlongVFSection (I := I) (M := M) g T.toSection B)
        (covDerivAlongVFSection (I := I) (M := M) g v.toSection B) b]
      rw [toModel_liftedTensorSection_covDerivAlongVFSection (I := I) (M := M) g T.toSection B b,
        toModel_liftedTensorSection_covDerivAlongVFSection (I := I) (M := M) g v.toSection B b]
  have haccel : g.inner b (Z b)
        ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
          ((B : ∀ y, TangentSpace I y) b)) =
      tensorInnerPointwise (I := I) (M := M) g 0 2 b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g 0 2 T b
            ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
              ((B : ∀ y, TangentSpace I y) b))))
        (TensorRSSpace.toModel (v.toSection b)) := by
    rw [hZ_def, dirichletVFSection_apply, inner_dirichletVF, dirichletForm_apply]
  have hsecond := covDerivAlong_covDerivAlongVFSection_eq (I := I) (M := M) g T.toSection B b
  have hsummand : g.inner b
        ((LeviCivita (I := I) g).toFun (fun y : M => Z y) b
          ((B : ∀ y, TangentSpace I y) b))
        ((B : ∀ y, TangentSpace I y) b) =
      tangentSectionAction (I := I) B (fun y : M => g.inner y (Z y) (B y)) b
        - g.inner b (Z b)
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
            ((B : ∀ y, TangentSpace I y) b)) := by
    rw [tangentSectionAction_def]
    rw [hleib]; ring
  change g.inner b
      ((LeviCivita (I := I) g).toFun (fun y : M => Z y) b
        ((B : ∀ y, TangentSpace I y) b))
      ((B : ∀ y, TangentSpace I y) b) = _
  rw [hsummand, hprod, haccel]
  rw [hsecond, TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  have haccel_eq :
      (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b (B b)) =
        tensorCovDerivAt (I := I) (M := M) g 0 2 T b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
            ((B : ∀ y, TangentSpace I y) b)) := rfl
  rw [haccel_eq]
  rw [show covDerivAlongVFSection (I := I) (M := M) g T.toSection B b =
        tensorCovDerivAt (I := I) (M := M) g 0 2 T b ((B : ∀ y, TangentSpace I y) b) from rfl,
    show covDerivAlongVFSection (I := I) (M := M) g v.toSection B b =
        tensorCovDerivAt (I := I) (M := M) g 0 2 v b ((B : ∀ y, TangentSpace I y) b) from rfl]
  rw [hBb]
  rw [show (fun y : M => (B : ∀ z : M, TangentSpace I z) y) =
        (fun y : M => smoothOrthoFrame (I := I) g b i y) from rfl]
  ring

omit [CompactSpace M] [BoundarylessManifold I M] in
private lemma tensorCovDerivPointwiseInner_eq_smoothOrthoFrame_diag
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 2 T b
              (smoothOrthoFrame (I := I) g b i b)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g 0 2 v b
              (smoothOrthoFrame (I := I) g b i b))) := by
  classical
  have hB_orth : ∀ i j, g.inner b
      (smoothOrthoFrame (I := I) g b i b) (smoothOrthoFrame (I := I) g b j b) =
      if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g b i j
  have hB_li : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) => smoothOrthoFrame (I := I) g b i b) := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner b (smoothOrthoFrame (I := I) g b k b)
        (∑ j ∈ fs, c j • smoothOrthoFrame (I := I) g b j b) = 0 := by
      rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs,
        g.inner b (smoothOrthoFrame (I := I) g b k b)
          (c j • smoothOrthoFrame (I := I) g b j b) =
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) := by
      intro j _
      rw [(g.inner b (smoothOrthoFrame (I := I) g b k b)).map_smul
        (c j) (smoothOrthoFrame (I := I) g b j b), smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    have h_pull2 : ∀ j ∈ fs,
        c j * g.inner b (smoothOrthoFrame (I := I) g b k b)
          (smoothOrthoFrame (I := I) g b j b) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [hB_orth k j]
    rw [Finset.sum_congr rfl h_pull2] at h_zero
    rw [Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rw [if_pos rfl, mul_one] at h_zero
      exact h_zero
    · intro j _ hjk
      rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E := by
    rw [Fintype.card_fin]
  set frame : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    basisOfLinearIndependentOfCardEqFinrank hB_li hcard with hframe_def
  have hframe_eq : ∀ i, frame i = smoothOrthoFrame (I := I) g b i b := by
    intro i
    rw [hframe_def]
    change (basisOfLinearIndependentOfCardEqFinrank hB_li hcard :
        Fin (Module.finrank ℝ E) → E) i = smoothOrthoFrame (I := I) g b i b
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hframe_orth : ∀ i j,
      g.inner b (frame i) (frame j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hframe_eq i, hframe_eq j]
    exact hB_orth i j
  rw [tensorCovDerivPointwiseInner_eq_orthoFrame_diag_sum
    (I := I) (M := M) g 0 2 T v b frame hframe_orth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hframe_eq i]

omit [CompactSpace M] in
lemma divergence_dirichletVF_eq
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) (b : M) :
    divergence_g (I := I) g (dirichletVFSection (I := I) (M := M) g T v) b =
      tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b
        + tensorInnerPointwise (I := I) (M := M) g 0 2 b
            (TensorRSSpace.toModel
              (rawTensorConnLap (I := I) g 0 2 (fun y : M => T.toSection y) b))
            (TensorRSSpace.toModel (v.toSection b)) := by
  classical
  rw [divergence_g_eq_smoothOrthoFrame_trace (I := I) g
    (dirichletVFSection (I := I) (M := M) g T v) b]
  rw [Finset.sum_congr rfl (fun i _ =>
    divergence_dirichletVF_summand_eq (I := I) (M := M) g T v b i)]
  rw [Finset.sum_add_distrib]
  rw [← tensorCovDerivPointwiseInner_eq_smoothOrthoFrame_diag (I := I) (M := M) g T v b]
  rw [add_comm]
  congr 1
  rw [rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g 0 2
    (fun y : M => T.toSection y) b]
  rw [show TensorRSSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          tensorSecondCovDeriv (I := I) g 0 2
            (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
            (fun y : M => T.toSection y) b) =
      ∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel
          (tensorSecondCovDeriv (I := I) g 0 2
            (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
            (fun y : M => T.toSection y) b) from ?_]
  · rw [show (∑ i : Fin (Module.finrank ℝ E),
            TensorRSSpace.toModel
              (tensorSecondCovDeriv (I := I) g 0 2
                (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
                (fun y : M => T.toSection y) b)) =
          ∑ i : Fin (Module.finrank ℝ E), (1 : ℝ) •
            TensorRSSpace.toModel
              (tensorSecondCovDeriv (I := I) g 0 2
                (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
                (fun y : M => T.toSection y) b) from by
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_smul]]
    rw [tensorInnerPointwise_sum_left (I := I) (M := M) g 0 2 b Finset.univ _ _ _]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [one_mul]
  · exact map_sum (tensorRSSpace_continuousLinearEquiv (I := I) 0 2 b)
      (fun i => tensorSecondCovDeriv (I := I) g 0 2
        (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
        (fun y : M => T.toSection y) b) Finset.univ

theorem green_first_covGrad_l2Inner_eq_neg_rawTensorConnLap_of_closed
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) :
    tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
        (covGrad (I := I) (M := M) g 0 2 T).toFun
        (covGrad (I := I) (M := M) g 0 2 v).toFun =
      - tensorL2Inner (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun v.toFun := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    dirichletVFSection (I := I) (M := M) g T v with hZ_def
  have hZ_cs : HasCompactSupport (Z : ∀ x, TangentSpace I x) :=
    HasCompactSupport.of_compactSpace _
  have hdiv_zero : ∫ b, divergence_g (I := I) g Z b ∂μ = 0 :=
    integral_divergence_eq_zero_of_hasCompactSupport (I := I) g Z hZ_cs
  have hpt : ∀ b : M, divergence_g (I := I) g Z b =
      tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b
        + tensorInnerPointwise (I := I) (M := M) g 0 2 b
            (TensorRSSpace.toModel
              (rawTensorConnLap (I := I) g 0 2 (fun y : M => T.toSection y) b))
            (TensorRSSpace.toModel (v.toSection b)) := by
    intro b; rw [hZ_def]; exact divergence_dirichletVF_eq (I := I) (M := M) g T v b
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)] at hdiv_zero
  have hcross_cont : Continuous
      (fun b : M => tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b) := by
    rw [show (fun b : M => tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b) =
          fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 (2 + 1) b
            (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 2 T).toSection b))
            (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g 0 2 v).toSection b)) from by
      funext b
      exact (tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad
        (I := I) (M := M) g 0 2 T v b)]
    exact (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 (2 + 1)
      (covGrad (I := I) (M := M) g 0 2 T).toSection
      (covGrad (I := I) (M := M) g 0 2 v).toSection).continuous
  have hsecond_cont : Continuous
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (rawTensorConnLap (I := I) g 0 2 (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b))) := by
    rw [show (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 2 b
            (TensorRSSpace.toModel
              (rawTensorConnLap (I := I) g 0 2 (fun y : M => T.toSection y) b))
            (TensorRSSpace.toModel (v.toSection b))) =
          fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 2 b
            (TensorRSSpace.toModel
              ((rawTensorConnLapSmooth (I := I) g 0 2 T).toSection b))
            (TensorRSSpace.toModel (v.toSection b)) from by
      funext b
      rw [rawTensorConnLapSmooth_toSection_apply (I := I) g 0 2 T b]]
    exact (tensorInnerScalar_contMDiff (I := I) (M := M) g 0 2
      (rawTensorConnLapSmooth (I := I) g 0 2 T).toSection v.toSection).continuous
  have hcross_int : Integrable
      (fun b : M => tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v b) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hcross_cont (HasCompactSupport.of_compactSpace _)
  have hsecond_int : Integrable
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (rawTensorConnLap (I := I) g 0 2 (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b))) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hsecond_cont (HasCompactSupport.of_compactSpace _)
  rw [integral_add hcross_int hsecond_int] at hdiv_zero
  rw [tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
    (I := I) (M := M) g 0 2 T v, ← hμ_def]
  rw [show tensorL2Inner (I := I) (M := M) g 0 2
        (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun v.toFun =
      ∫ b, tensorInnerPointwise (I := I) (M := M) g 0 2 b
          (TensorRSSpace.toModel
            (rawTensorConnLap (I := I) g 0 2 (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b)) ∂μ from ?_]
  · linarith [hdiv_zero]
  · unfold tensorL2Inner
    rw [← hμ_def]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun b => ?_))
    simp only [SmoothCcTensor.toFun_apply, rawTensorConnLapSmooth_toSection_apply]

end Connection
end Integral
end DifferentialGeometry

end
