import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.TensorConnLapGreenIntertwiner


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
  [FiniteDimensional ℝ E]
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

def LoweringIntertwinerRS (g : SmoothRiemannianMetric I M) (r s : ℕ) : Prop :=
  ∀ (S : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (x : M) (v : TangentSpace I x),
    Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g r s S x v) =
      lowerAllUpperIndices (I := I) (M := M) g r s x
        (TensorRSSpace.toModel
          (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) S x v))

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem loweringIntertwinerRS_holds (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    LoweringIntertwinerRS (I := I) (M := M) g r s :=
  fun S x v => loweredCovDerivAt_eq_lower_tensorCovDerivAt_rs (I := I) (M := M) g r s S x v

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem loweringIntertwinerRS_zero (g : SmoothRiemannianMetric I M) (s : ℕ) :
    LoweringIntertwinerRS (I := I) (M := M) g 0 s :=
  fun S x v => loweredCovDerivAt_eq_lower_tensorCovDerivAt_gen (I := I) (M := M) g s S x v

def covDerivAlongVFrawRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Π y : M, TensorRSSpace r s I y :=
  covApply (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g))
    (fun y : M => B y) (fun y : M => T y)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma covDerivAlongVFrawRS_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFrawRS (I := I) (M := M) g r s T B y =
      (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) y (B y) := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlongVFrawRS_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covDerivAlongVFrawRS (I := I) (M := M) g r s T B y)) := by
  classical
  set cov := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) with hcov_def
  have hT : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      ((∞ : WithTop ℕ∞) + 1)
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)) := by
    rw [show ((∞ : WithTop ℕ∞) + 1) = (∞ : WithTop ℕ∞) from rfl]
    exact T.contMDiff
  have hB : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (B y)) :=
    B.contMDiff
  have hOn : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y
        (covApply cov (fun y : M => B y) (fun y : M => T y) y)) Set.univ :=
    covApply_contMDiffOn (cov := cov) hB hT
  rw [← contMDiffOn_univ]
  exact hOn

def covDerivAlongVFSectionRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯ :=
  ContMDiffSection.mk
    (fun y : M => covDerivAlongVFrawRS (I := I) (M := M) g r s T B y)
    (covDerivAlongVFrawRS_contMDiff (I := I) (M := M) g r s T B)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma covDerivAlongVFSectionRS_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFSectionRS (I := I) (M := M) g r s T B y =
      (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
        (fun y : M => T y) y (B y) := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlongVFSectionRS_lowered_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (hint : LoweringIntertwinerRS (I := I) (M := M) g r s)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    lowerAllUpperIndices (I := I) (M := M) g r s y
        (TensorRSSpace.toModel (covDerivAlongVFSectionRS (I := I) (M := M) g r s T B y)) =
      Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g r s T y (B y)) := by
  rw [hint T y (B y)]
  rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma toModel_liftedTensorSection_covDerivAlongVFSectionRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (hint : LoweringIntertwinerRS (I := I) (M := M) g r s)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    Tensor0SSpace.toModel
        (liftedTensorSection (I := I) (M := M) g r s
          (covDerivAlongVFSectionRS (I := I) (M := M) g r s T B) y) =
      Tensor0SSpace.toModel (loweredCovDerivAt (I := I) (M := M) g r s T y (B y)) := by
  rw [toModel_liftedTensorSection]
  exact covDerivAlongVFSectionRS_lowered_eq (I := I) (M := M) g r s hint T B y

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlongRS_covDerivAlongVFSectionRS_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (y : M) :
    covDerivAlongVFSectionRS (I := I) (M := M) g r s
        (covDerivAlongVFSectionRS (I := I) (M := M) g r s T B) B y =
      tensorSecondCovDeriv (I := I) g r s
          (fun b : M => B b) (fun b : M => B b) (fun b : M => T b) y +
        (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
          (fun b : M => T b) y
          ((LeviCivita (I := I) g).toFun (fun b : M => B b) y (B y)) := by
  rw [tensorSecondCovDeriv_def]
  change (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
      (covApply (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g))
        (fun b : M => B b) (fun b : M => T b)) y (B y) = _
  rw [show tensorCov (I := I) g r s =
      tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g) from rfl]
  abel

def dirichletFormRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) (b : M) :
    TangentSpace I b →ₗ[ℝ] ℝ where
  toFun X := tensorInnerPointwise (I := I) (M := M) g r s b
    (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g r s T b X))
    (TensorRSSpace.toModel (v.toSection b))
  map_add' X Y := by
    have hcov : tensorCovDerivAt (I := I) (M := M) g r s T b (X + Y) =
        tensorCovDerivAt (I := I) (M := M) g r s T b X +
          tensorCovDerivAt (I := I) (M := M) g r s T b Y := by
      change (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b (X + Y) = _
      rw [ContinuousLinearMap.map_add]
      rfl
    rw [hcov, TensorRSSpace.toModel_add, tensorInnerPointwise_add_left]
  map_smul' c X := by
    have hcov : tensorCovDerivAt (I := I) (M := M) g r s T b (c • X) =
        c • tensorCovDerivAt (I := I) (M := M) g r s T b X := by
      change (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b (c • X) = _
      rw [ContinuousLinearMap.map_smul]
      rfl
    rw [hcov, TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left]
    rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma dirichletFormRS_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) (b : M)
    (X : TangentSpace I b) :
    dirichletFormRS (I := I) (M := M) g r s T v b X =
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel (tensorCovDerivAt (I := I) (M := M) g r s T b X))
        (TensorRSSpace.toModel (v.toSection b)) := rfl

def dirichletVFRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) (b : M) :
    TangentSpace I b :=
  metricSharp (I := I) g b (dirichletFormRS (I := I) (M := M) g r s T v b)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma inner_dirichletVFRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) (b : M)
    (X : TangentSpace I b) :
    g.inner b (dirichletVFRS (I := I) (M := M) g r s T v b) X =
      dirichletFormRS (I := I) (M := M) g r s T v b X := by
  rw [dirichletVFRS]
  exact inner_metricSharp (I := I) g b (dirichletFormRS (I := I) (M := M) g r s T v b) X

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma dirichletFormRS_chartBasis_component_contMDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => dirichletFormRS (I := I) (M := M) g r s T v b
        (chartBasisVecFiber (I := I) α j b))
      (chartAt H α).source := by
  have hcov_section : ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun y : M => TensorRSSpace r s I y) b
        (tensorCovDerivAt (I := I) (M := M) g r s T b
          (chartBasisVecFiber (I := I) α j b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    tensorCovDeriv_chartBasis_contMDiffOn (I := I) (M := M) g r s T α j
  have hcov_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b
            (chartBasisVecFiber (I := I) α j b))))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose_of_section_contMDiffOn
      (I := I) (M := M) g r s
      (fun b : M => tensorCovDerivAt (I := I) (M := M) g r s T b
        (chartBasisVecFiber (I := I) α j b)) α hcov_section
  have hv_lowered : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel (v.toSection b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    TensorMetricLowering.contMDiffOn_loweredCompose (I := I) (M := M) g r s v.toSection α
  have hinner : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s T b
              (chartBasisVecFiber (I := I) α j b)))
          (TensorRSSpace.toModel (v.toSection b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections
      (I := I) (M := M) g r s
      (fun b : M => tensorCovDerivAt (I := I) (M := M) g r s T b
        (chartBasisVecFiber (I := I) α j b))
      (fun b : M => v.toSection b) α hcov_lowered hv_lowered
  have hbase_eq : (trivializationAt E (TangentSpace I) α).baseSet =
      (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
      (I := I) α
  rw [hbase_eq] at hinner
  refine hinner.congr ?_
  intro b _
  rw [dirichletFormRS_apply]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma dirichletVFRS_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E b (dirichletVFRS (I := I) (M := M) g r s T v b)) :=
  metricSharp_contMDiff_total (I := I) g
    (cv := fun b : M => dirichletFormRS (I := I) (M := M) g r s T v b)
    (fun α j => dirichletFormRS_chartBasis_component_contMDiffOn
      (I := I) (M := M) g r s T v α j)

def dirichletVFSectionRS
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ContMDiffSection.mk
    (fun b : M => dirichletVFRS (I := I) (M := M) g r s T v b)
    (dirichletVFRS_contMDiff (I := I) (M := M) g r s T v)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma dirichletVFSectionRS_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) (b : M) :
    dirichletVFSectionRS (I := I) (M := M) g r s T v b =
      dirichletVFRS (I := I) (M := M) g r s T v b := rfl

omit [CompactSpace M] in
private lemma divergence_dirichletVFRS_summand_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (hint : LoweringIntertwinerRS (I := I) (M := M) g r s)
    (T v : SmoothCcTensor g r s) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    g.inner b
        ((LeviCivita (I := I) g).toFun
          (dirichletVFSectionRS (I := I) (M := M) g r s T v).toFun b
          (smoothOrthoFrame (I := I) g b i b))
        (smoothOrthoFrame (I := I) g b i b) =
      tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (tensorSecondCovDeriv (I := I) g r s
              (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
              (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s T b
              (smoothOrthoFrame (I := I) g b i b)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s v b
              (smoothOrthoFrame (I := I) g b i b))) := by
  classical
  set B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun y : M => smoothOrthoFrame (I := I) g b i y,
      smoothOrthoFrame_smooth (I := I) g b i⟩ with hB_def
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    dirichletVFSectionRS (I := I) (M := M) g r s T v with hZ_def
  have hBb : (B : ∀ y, TangentSpace I y) b = smoothOrthoFrame (I := I) g b i b := rfl
  have hleib := leibniz_inner (I := I) g
    (V := fun y : M => Z y) (W := fun y : M => B y)
    Z.contMDiff B.contMDiff
    (x := b) ((B : ∀ y, TangentSpace I y) b)
  have hfun : (fun y : M => g.inner y (Z y) (B y)) =
      tensorInnerScalar (I := I) (M := M) g r s
        (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B) v.toSection := by
    funext y
    rw [hZ_def, dirichletVFSectionRS_apply, inner_dirichletVFRS, dirichletFormRS_apply,
      tensorInnerScalar_apply, covDerivAlongVFSectionRS_apply]
    rfl
  have hprod : tangentSectionAction (I := I) B
        (fun y : M => g.inner y (Z y) (B y)) b =
      tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionRS (I := I) (M := M) g r s
              (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B) B b))
          (TensorRSSpace.toModel (v.toSection b))
        + tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B b))
          (TensorRSSpace.toModel
            (covDerivAlongVFSectionRS (I := I) (M := M) g r s v.toSection B b)) := by
    rw [show tangentSectionAction (I := I) B
            (fun y : M => g.inner y (Z y) (B y)) =
          tangentSectionAction (I := I) B
            (tensorInnerScalar (I := I) (M := M) g r s
              (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B) v.toSection) from by
      rw [hfun]]
    rw [tangentSectionAction_tensorInnerScalar (I := I) (M := M) g r s
      (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B) v.toSection B b]
    congr 1
    · rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g r s
        (covDerivAlongVFSectionRS (I := I) (M := M) g r s
          (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B) B)
        v.toSection b]
      rw [toModel_liftedTensorSection_covDerivAlongVFSectionRS (I := I) (M := M) g r s hint
        (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B) B b]
    · rw [tensorInnerPointwise_eq_liftedTensorSection_inner (I := I) (M := M) g r s
        (covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B)
        (covDerivAlongVFSectionRS (I := I) (M := M) g r s v.toSection B) b]
      rw [toModel_liftedTensorSection_covDerivAlongVFSectionRS (I := I) (M := M) g r s hint T.toSection B b,
        toModel_liftedTensorSection_covDerivAlongVFSectionRS (I := I) (M := M) g r s hint v.toSection B b]
  have haccel : g.inner b (Z b)
        ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
          ((B : ∀ y, TangentSpace I y) b)) =
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s T b
            ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
              ((B : ∀ y, TangentSpace I y) b))))
        (TensorRSSpace.toModel (v.toSection b)) := by
    rw [hZ_def, dirichletVFSectionRS_apply, inner_dirichletVFRS, dirichletFormRS_apply]
  have hsecond := covDerivAlongRS_covDerivAlongVFSectionRS_eq (I := I) (M := M) g r s T.toSection B b
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
      (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
          (fun y : M => T.toSection y) b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b (B b)) =
        tensorCovDerivAt (I := I) (M := M) g r s T b
          ((LeviCivita (I := I) g).toFun (fun y : M => B y) b
            ((B : ∀ y, TangentSpace I y) b)) := rfl
  rw [haccel_eq]
  rw [show covDerivAlongVFSectionRS (I := I) (M := M) g r s T.toSection B b =
        tensorCovDerivAt (I := I) (M := M) g r s T b ((B : ∀ y, TangentSpace I y) b) from rfl,
    show covDerivAlongVFSectionRS (I := I) (M := M) g r s v.toSection B b =
        tensorCovDerivAt (I := I) (M := M) g r s v b ((B : ∀ y, TangentSpace I y) b) from rfl]
  rw [hBb]
  rw [show (fun y : M => (B : ∀ z : M, TangentSpace I z) y) =
        (fun y : M => smoothOrthoFrame (I := I) g b i y) from rfl]
  ring

omit [BoundarylessManifold I M] in
omit [CompactSpace M] in
private lemma tensorCovDerivPointwiseInnerRS_eq_smoothOrthoFrame_diag
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T v : SmoothCcTensor g r s) (b : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v b =
      ∑ i : Fin (Module.finrank ℝ E),
        tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s T b
              (smoothOrthoFrame (I := I) g b i b)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s v b
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
    (I := I) (M := M) g r s T v b frame hframe_orth]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hframe_eq i]

omit [CompactSpace M] in
lemma divergence_dirichletVFRS_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (hint : LoweringIntertwinerRS (I := I) (M := M) g r s)
    (T v : SmoothCcTensor g r s) (b : M) :
    divergence_g (I := I) g (dirichletVFSectionRS (I := I) (M := M) g r s T v) b =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v b
        + tensorInnerPointwise (I := I) (M := M) g r s b
            (TensorRSSpace.toModel
              (rawTensorConnLap (I := I) g r s (fun y : M => T.toSection y) b))
            (TensorRSSpace.toModel (v.toSection b)) := by
  classical
  rw [divergence_g_eq_smoothOrthoFrame_trace (I := I) g
    (dirichletVFSectionRS (I := I) (M := M) g r s T v) b]
  rw [Finset.sum_congr rfl (fun i _ =>
    divergence_dirichletVFRS_summand_eq (I := I) (M := M) g r s hint T v b i)]
  rw [Finset.sum_add_distrib]
  rw [← tensorCovDerivPointwiseInnerRS_eq_smoothOrthoFrame_diag (I := I) (M := M) g r s T v b]
  rw [add_comm]
  congr 1
  rw [rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g r s
    (fun y : M => T.toSection y) b]
  rw [show TensorRSSpace.toModel
        (∑ i : Fin (Module.finrank ℝ E),
          tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
            (fun y : M => T.toSection y) b) =
      ∑ i : Fin (Module.finrank ℝ E),
        TensorRSSpace.toModel
          (tensorSecondCovDeriv (I := I) g r s
            (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
            (fun y : M => T.toSection y) b) from ?_]
  · rw [show (∑ i : Fin (Module.finrank ℝ E),
            TensorRSSpace.toModel
              (tensorSecondCovDeriv (I := I) g r s
                (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
                (fun y : M => T.toSection y) b)) =
          ∑ i : Fin (Module.finrank ℝ E), (1 : ℝ) •
            TensorRSSpace.toModel
              (tensorSecondCovDeriv (I := I) g r s
                (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
                (fun y : M => T.toSection y) b) from by
      refine Finset.sum_congr rfl (fun i _ => ?_); rw [one_smul]]
    rw [tensorInnerPointwise_sum_left (I := I) (M := M) g r s b Finset.univ _ _ _]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [one_mul]
  · exact map_sum (tensorRSSpace_continuousLinearEquiv (I := I) r s b)
      (fun i => tensorSecondCovDeriv (I := I) g r s
        (smoothOrthoFrame (I := I) g b i) (smoothOrthoFrame (I := I) g b i)
        (fun y : M => T.toSection y) b) Finset.univ

theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (hint : LoweringIntertwinerRS (I := I) (M := M) g r s)
    (T v : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s T).toFun
        (covGrad (I := I) (M := M) g r s v).toFun =
      - tensorL2Inner (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  set Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    dirichletVFSectionRS (I := I) (M := M) g r s T v with hZ_def
  have hZ_cs : HasCompactSupport (Z : ∀ x, TangentSpace I x) :=
    HasCompactSupport.of_compactSpace _
  have hdiv_zero : ∫ b, divergence_g (I := I) g Z b ∂μ = 0 :=
    integral_divergence_eq_zero_of_hasCompactSupport (I := I) g Z hZ_cs
  have hpt : ∀ b : M, divergence_g (I := I) g Z b =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v b
        + tensorInnerPointwise (I := I) (M := M) g r s b
            (TensorRSSpace.toModel
              (rawTensorConnLap (I := I) g r s (fun y : M => T.toSection y) b))
            (TensorRSSpace.toModel (v.toSection b)) := by
    intro b; rw [hZ_def]; exact divergence_dirichletVFRS_eq (I := I) (M := M) g r s hint T v b
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)] at hdiv_zero
  have hcross_cont : Continuous
      (fun b : M => tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v b) := by
    rw [show (fun b : M => tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v b) =
          fun b : M => tensorInnerPointwise (I := I) (M := M) g r (s + 1) b
            (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g r s T).toSection b))
            (TensorRSSpace.toModel ((covGrad (I := I) (M := M) g r s v).toSection b)) from by
      funext b
      exact (tensorCovDerivPointwiseInner_eq_tensorInnerPointwise_grad
        (I := I) (M := M) g r s T v b)]
    exact (tensorInnerScalar_contMDiff (I := I) (M := M) g r (s + 1)
      (covGrad (I := I) (M := M) g r s T).toSection
      (covGrad (I := I) (M := M) g r s v).toSection).continuous
  have hsecond_cont : Continuous
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (rawTensorConnLap (I := I) g r s (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b))) := by
    rw [show (fun b : M => tensorInnerPointwise (I := I) (M := M) g r s b
            (TensorRSSpace.toModel
              (rawTensorConnLap (I := I) g r s (fun y : M => T.toSection y) b))
            (TensorRSSpace.toModel (v.toSection b))) =
          fun b : M => tensorInnerPointwise (I := I) (M := M) g r s b
            (TensorRSSpace.toModel
              ((rawTensorConnLapSmooth (I := I) g r s T).toSection b))
            (TensorRSSpace.toModel (v.toSection b)) from by
      funext b
      rw [rawTensorConnLapSmooth_toSection_apply (I := I) g r s T b]]
    exact (tensorInnerScalar_contMDiff (I := I) (M := M) g r s
      (rawTensorConnLapSmooth (I := I) g r s T).toSection v.toSection).continuous
  have hcross_int : Integrable
      (fun b : M => tensorCovDerivPointwiseInner (I := I) (M := M) g r s T v b) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hcross_cont (HasCompactSupport.of_compactSpace _)
  have hsecond_int : Integrable
      (fun b : M => tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (rawTensorConnLap (I := I) g r s (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b))) μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hsecond_cont (HasCompactSupport.of_compactSpace _)
  rw [integral_add hcross_int hsecond_int] at hdiv_zero
  rw [tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
    (I := I) (M := M) g r s T v, ← hμ_def]
  rw [show tensorL2Inner (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun =
      ∫ b, tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (rawTensorConnLap (I := I) g r s (fun y : M => T.toSection y) b))
          (TensorRSSpace.toModel (v.toSection b)) ∂μ from ?_]
  · linarith [hdiv_zero]
  · unfold tensorL2Inner
    rw [← hμ_def]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun b => ?_))
    simp only [SmoothCcTensor.toFun_apply, rawTensorConnLapSmooth_toSection_apply]

theorem tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T v : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r (s + 1)
        (covGrad (I := I) (M := M) g r s T).toFun
        (covGrad (I := I) (M := M) g r s v).toFun =
      - tensorL2Inner (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T).toFun v.toFun :=
  tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawTensorConnLapSmooth_rs_of_intertwiner
    (I := I) (M := M) g r s (loweringIntertwinerRS_holds (I := I) (M := M) g r s) T v

end Connection
end Integral
end DifferentialGeometry

end
