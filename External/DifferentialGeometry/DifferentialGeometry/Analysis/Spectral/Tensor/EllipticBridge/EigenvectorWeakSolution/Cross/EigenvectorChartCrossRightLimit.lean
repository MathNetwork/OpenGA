import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cross.EigenvectorChartCrossLimits
import DifferentialGeometry.Geometry.Operator.Gradient


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorRSNabla
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma extDerivFun_apply_scalar (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    extDerivFun (I := I) f x v = mfderiv I 𝓘(ℝ, ℝ) f x v := by
  simp only [extDerivFun, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk]
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma tensorCovDerivAt_zero_dir
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivAt (I := I) (M := M) g r s S x (0 : E) = 0 := by
  rw [tensorCovDerivAt_def]
  exact ContinuousLinearMap.map_zero _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma gradFun_eq_gramInv_sum
    (g : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; ℝ⟯) (x : M) :
    gradFun (I := I) g (ζ : M → ℝ) x =
      ∑ j : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E),
          (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
          (chartModelBasis E) j := by
  classical
  set Ginv := (gramMatrixAt (I := I) (M := M) g x)⁻¹ with hGinv
  set rhs : TangentSpace I x :=
    ∑ j : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E),
        Ginv i j * extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
        (chartModelBasis E) j with hrhs
  refine (DifferentialGeometry.Integral.Connection.metricFlatLinear_injective
    (I := I) g x ?_).symm
  refine (chartModelBasis E).ext ?_
  intro k
  have hgrad_k : DifferentialGeometry.Integral.Connection.metricFlatLinear (I := I) g x
      (gradFun (I := I) g (ζ : M → ℝ) x) ((chartModelBasis E) k) =
        extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) k) := by
    rw [DifferentialGeometry.Integral.Connection.metricFlatLinear_apply, extDerivFun_apply_scalar]
    exact inner_gradFun (I := I) g (ζ : M → ℝ) x ((chartModelBasis E) k)
  have hrhs_k : DifferentialGeometry.Integral.Connection.metricFlatLinear (I := I) g x rhs ((chartModelBasis E) k) =
      ∑ j : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E),
          Ginv i j * extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) *
          gramMatrixAt (I := I) (M := M) g x j k := by
    rw [DifferentialGeometry.Integral.Connection.metricFlatLinear_apply, hrhs]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, gramMatrixAt_apply]
  have hgram : ∀ i : Fin (Module.finrank ℝ E),
      (∑ j : Fin (Module.finrank ℝ E),
        Ginv i j * gramMatrixAt (I := I) (M := M) g x j k) =
        (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) i k := by
    intro i
    have hmul := gramMatrixAt_inv_mul_self (I := I) (M := M) g x
    have hentry := congrFun (congrFun hmul i) k
    rw [Matrix.mul_apply] at hentry
    rw [hGinv]
    exact hentry
  calc DifferentialGeometry.Integral.Connection.metricFlatLinear (I := I) g x rhs ((chartModelBasis E) k)
      = ∑ j : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E),
            Ginv i j *
              extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) *
            gramMatrixAt (I := I) (M := M) g x j k := hrhs_k
    _ = ∑ j : Fin (Module.finrank ℝ E),
          ∑ i : Fin (Module.finrank ℝ E),
            extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i) *
              (Ginv i j * gramMatrixAt (I := I) (M := M) g x j k) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
    _ = ∑ i : Fin (Module.finrank ℝ E),
          extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i) *
            (∑ j : Fin (Module.finrank ℝ E),
              Ginv i j * gramMatrixAt (I := I) (M := M) g x j k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ i : Fin (Module.finrank ℝ E),
          extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i) *
            (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
              i k := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hgram i]
    _ = extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) k) := by
        rw [Finset.sum_eq_single k]
        · rw [Matrix.one_apply_eq, mul_one]
        · intro i _ hik
          rw [Matrix.one_apply_ne hik, mul_zero]
        · intro hk
          exact absurd (Finset.mem_univ k) hk
    _ = DifferentialGeometry.Integral.Connection.metricFlatLinear (I := I) g x
          (gradFun (I := I) g (ζ : M → ℝ) x) ((chartModelBasis E) k) :=
        hgrad_k.symm

private noncomputable def covDerivHomSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    Π x : M, TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
  fun x => tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
    (fun y : M => S.toSection y) x

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivHomSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (x : M) (v : E) :
    covDerivHomSection (I := I) (M := M) g r s S x v =
      tensorCovDerivAt (I := I) (M := M) g r s S x v := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivHomSection_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M =>
        (⟨x, covDerivHomSection (I := I) (M := M) g r s S x⟩ :
          TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
            fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)) := by
  classical
  set covLC := tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
    with hcovLC
  haveI hcovLC_inst : CovariantDerivative.ContMDiffCovariantDerivative covLC ∞ :=
    inferInstance
  have hop : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M => (⟨x, covLC.toFun (fun y : M => S.toSection y) x⟩ :
        TotalSpace (E →L[ℝ] TensorRSModel r s ℝ E)
          fun y : M => TangentSpace I y →L[ℝ] TensorRSSpace r s I y)) Set.univ :=
    hcovLC_inst.contMDiff.contMDiff (σ := fun y : M => S.toSection y)
      (S.toSection.contMDiff.contMDiffOn)
  rw [← contMDiffOn_univ]
  exact hop

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivAlong_section_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M =>
        (⟨x, tensorCovDerivAt (I := I) (M := M) g r s S x (V x)⟩ :
          TotalSpace (TensorRSModel r s ℝ E)
            fun y : M => TensorRSSpace r s I y)) := by
  have hϕ := covDerivHomSection_contMDiff (I := I) (M := M) g r s S
  have hv : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, V x⟩ :
        TotalSpace E (TangentSpace I : M → Type _))) :=
    V.contMDiff
  exact ContMDiff.clm_bundle_apply hϕ hv

private noncomputable def covDerivAlongSection
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯ :=
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  letI : TopologicalSpace (TotalSpace (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y)) :=
    tensorRSBundle_topology r s
  letI : FiberBundle (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_fiber r s
  letI : VectorBundle ℝ (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_vector r s
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) I :=
    tensorRSBundle_smooth ∞ r s
  (ContMDiffSection.mk
      (fun x : M => tensorCovDerivAt (I := I) (M := M) g r s S x (V x))
      (covDerivAlong_section_contMDiff (I := I) (M := M) g r s S V) :
    Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivAlongSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    covDerivAlongSection (I := I) (M := M) g r s S V x =
      tensorCovDerivAt (I := I) (M := M) g r s S x (V x) := rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivAlongSection_toModel_eq_zero_off_tsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) {x : M}
    (hx : x ∉ tsupport S.toFun) :
    TensorRSSpace.toModel
      (covDerivAlongSection (I := I) (M := M) g r s S V x) = 0 := by
  rw [covDerivAlongSection_apply,
    tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g r s S hx (V x),
    TensorRSSpace.toModel_zero]

omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivAlongSection_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    HasCompactSupport
      (fun x : M => TensorRSSpace.toModel
        (covDerivAlongSection (I := I) (M := M) g r s S V x)) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact S.hasCompactSupport ?_
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxnot
  exact hx (covDerivAlongSection_toModel_eq_zero_off_tsupport
    (I := I) (M := M) g r s S V hxnot)

noncomputable def covDerivAlong
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    SmoothCcTensor g r s where
  toSection := covDerivAlongSection (I := I) (M := M) g r s S V
  hasCompactSupport :=
    covDerivAlongSection_hasCompactSupport (I := I) (M := M) g r s S V

omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlong_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (covDerivAlong (I := I) (M := M) g r s S V).toSection x =
      tensorCovDerivAt (I := I) (M := M) g r s S x (V x) := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlong_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    (covDerivAlong (I := I) (M := M) g r s S V).toFun x =
      TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S x (V x)) := by
  rw [SmoothCcTensor.toFun_apply, covDerivAlong_toSection_apply]

omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlong_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    tsupport (covDerivAlong (I := I) (M := M) g r s S V).toFun ⊆
      tsupport S.toFun := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxnot
  refine hx ?_
  rw [covDerivAlong_toFun_apply,
    tensorCovDerivAt_eq_zero_off_tsupport (I := I) (M := M) g r s S hxnot (V x),
    TensorRSSpace.toModel_zero]

noncomputable def covDerivAlongGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (ζ : C^∞⟮I, M; ℝ⟯) :
    SmoothCcTensor g r s :=
  covDerivAlong (I := I) (M := M) g r s S
    (grad_g (I := I) g ζ.contMDiff)

omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlongGrad_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (ζ : C^∞⟮I, M; ℝ⟯) (x : M) :
    (covDerivAlongGrad (I := I) (M := M) g r s S ζ).toSection x =
      tensorCovDerivAt (I := I) (M := M) g r s S x
        (gradFun (I := I) g (ζ : M → ℝ) x) := by
  rw [covDerivAlongGrad, covDerivAlong_toSection_apply, grad_g_apply]

omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlongGrad_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (ζ : C^∞⟮I, M; ℝ⟯) (x : M) :
    (covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun x =
      TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S x
          (gradFun (I := I) g (ζ : M → ℝ) x)) := by
  rw [SmoothCcTensor.toFun_apply, covDerivAlongGrad_toSection_apply]

omit [NeZero (Module.finrank ℝ E)] in
lemma covDerivAlongGrad_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (ζ : C^∞⟮I, M; ℝ⟯) :
    tsupport (covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun ⊆
      tsupport ((ζ : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxnot
  refine hx ?_
  have hgrad_zero : gradFun (I := I) g (ζ : M → ℝ) x = (0 : TangentSpace I x) := by
    by_contra hne
    exact hxnot (support_gradFun_subset (I := I) g (ζ : M → ℝ)
      (by rw [Function.mem_support]; exact hne))
  rw [covDerivAlongGrad_toFun_apply, hgrad_zero,
    tensorCovDerivAt_zero_dir (I := I) (M := M) g r s S x,
    TensorRSSpace.toModel_zero]

private noncomputable def tensorInnerPointwiseRightHom
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : TensorRSModel r s ℝ E) :
    TensorRSModel r s ℝ E →+ ℝ where
  toFun := fun T => tensorInnerPointwise (I := I) (M := M) g r s x A T
  map_zero' := tensorInnerPointwise_zero_right (I := I) (M := M) g r s x A
  map_add' := tensorInnerPointwise_add_right (I := I) (M := M) g r s x A

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorInnerPointwise_sum_sum_right
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : TensorRSModel r s ℝ E)
    (T : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s x A
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T i j) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          tensorInnerPointwise (I := I) (M := M) g r s x A (T i j) := by
  classical
  have h := map_sum (tensorInnerPointwiseRightHom (I := I) (M := M) g r s x A)
    (fun i => ∑ j : Fin (Module.finrank ℝ E), T i j) Finset.univ
  rw [show tensorInnerPointwise (I := I) (M := M) g r s x A
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T i j) =
      tensorInnerPointwiseRightHom (I := I) (M := M) g r s x A
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E), T i j) from rfl]
  rw [h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact map_sum (tensorInnerPointwiseRightHom (I := I) (M := M) g r s x A)
    (fun j => T i j) Finset.univ

omit [NeZero (Module.finrank ℝ E)] in
private lemma gramInv_sum_covDeriv_eq_covDerivAlongGrad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (S : SmoothCcTensor g r s) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
            TensorRSSpace.toModel
              (tensorCovDerivAt (I := I) (M := M) g r s S x
                ((chartModelBasis E) j)) =
      (covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun x := by
  classical
  set D : TangentSpace I x →L[ℝ] TensorRSSpace r s I x :=
    tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)
      (fun y : M => S.toSection y) x with hD
  set toM : TensorRSSpace r s I x ≃L[ℝ] TensorRSModel r s ℝ E :=
    tensorRSSpace_continuousLinearEquiv (I := I) r s x with htoM
  have hcov : ∀ v : E,
      tensorCovDerivAt (I := I) (M := M) g r s S x v = D v := fun v => rfl
  have hgoal_rhs :
      (covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun x =
        toM (D (gradFun (I := I) g (ζ : M → ℝ) x)) := by
    rw [covDerivAlongGrad_toFun_apply, hcov]
    rfl
  rw [hgoal_rhs]
  have htoModel_cov : ∀ j : Fin (Module.finrank ℝ E),
      TensorRSSpace.toModel
        (tensorCovDerivAt (I := I) (M := M) g r s S x ((chartModelBasis E) j)) =
        toM (D ((chartModelBasis E) j)) := by
    intro j
    rw [hcov]
    rfl
  have hlhs :
      ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
              extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
              TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) j)) =
        toM (D (∑ j : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E),
            (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
              extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
            (chartModelBasis E) j)) := by
    calc ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
              extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
              TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((chartModelBasis E) j))
        = ∑ j : Fin (Module.finrank ℝ E),
            ∑ i : Fin (Module.finrank ℝ E),
              ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
                extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
                toM (D ((chartModelBasis E) j)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [htoModel_cov j]
      _ = ∑ j : Fin (Module.finrank ℝ E),
            toM (D ((∑ i : Fin (Module.finrank ℝ E),
              (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
                extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
              (chartModelBasis E) j)) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [map_smul D, map_smul toM, Finset.sum_smul]
      _ = toM (D (∑ j : Fin (Module.finrank ℝ E),
            (∑ i : Fin (Module.finrank ℝ E),
              (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
                extDerivFun (I := I) (ζ : M → ℝ) x ((chartModelBasis E) i)) •
              (chartModelBasis E) j)) := by
          rw [map_sum D, map_sum toM]
  rw [hlhs]
  rw [← gradFun_eq_gramInv_sum (I := I) g ζ x]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (w.toFun x)
        ((covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun x) := by
  classical
  rw [tensorCovDerivCrossRight_def]
  rw [← gramInv_sum_covDeriv_eq_covDerivAlongGrad (I := I) (M := M) g r s ζ S x]
  rw [tensorInnerPointwise_sum_sum_right]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [tensorInnerPointwise_smul_right]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivCrossRight_integral_eq_innerLow
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) :
    ∫ x, tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ⟪(w : TensorL2 r s g),
        ((covDerivAlongGrad (I := I) (M := M) g r s S ζ :
          SmoothCcTensor g r s) : TensorL2 r s g)⟫_ℝ := by
  rw [UniformSpace.Completion.inner_coe,
    SmoothCcTensor.inner_def w
      (covDerivAlongGrad (I := I) (M := M) g r s S ζ),
    tensorL2Inner]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro x
  exact tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad
    (I := I) (M := M) g r s ζ w S x

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivCrossRight_integral_eq_chartPull
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (w S : SmoothCcTensor g r s) :
    ∫ x, tensorCovDerivCrossRight (I := I) (M := M) g r s
          (chartAtlasPOU I M α) w S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                  (w : TensorL2 r s g) α P :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y *
              tensorComponentEuclid (I := I) (M := M) g r s
                (covDerivAlongGrad (I := I) (M := M) g r s S
                  (chartAtlasPOU I M α)) α Q y)
        ∂(volume : Measure EuclN) := by
  rw [tensorCovDerivCrossRight_integral_eq_innerLow (I := I) (M := M) g r s
    (chartAtlasPOU I M α) w S]
  exact tensorL2Inner_cutoff_chartKernelSupported_pull (I := I) (M := M)
    g r s α (w : TensorL2 r s g)
    (covDerivAlongGrad (I := I) (M := M) g r s S (chartAtlasPOU I M α))
    (covDerivAlongGrad_tsupport_subset (I := I) (M := M) g r s S
      (chartAtlasPOU I M α))

theorem tensorL2_eigenvectorSmoothApprox_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Filter.Tendsto
      (fun n => (((eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor) : TensorL2 r s g))
      atTop
      (𝓝 (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i))) := by
  have h_clm :=
    ((TensorH1ComplToTensorL2 (I := I) (M := M) g r s).continuous.tendsto _).comp
      (eigenvectorSmoothApprox_tendsto (I := I) (M := M) g r s i)
  refine h_clm.congr ?_
  intro n
  rw [Function.comp_apply,
    TensorH1ComplToTensorL2_smoothToTensorH1Compl_eq_coe (I := I) (M := M) g r s
      (eigenvectorSmoothApprox (I := I) (M := M) g r s i n)]

def crossRightLimitComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : CompIdx E r s) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  tensorL2ChartComponentCutoff (I := I) (M := M) g r s
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s i))
    α P

theorem crossRightComponent_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : CompIdx E r s) :
    Filter.Tendsto
      (fun n => tensorL2ChartComponentCutoff (I := I) (M := M) g r s
        (((eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) : TensorL2 r s g)
        α P)
      atTop
      (𝓝 (crossRightLimitComponent (I := I) (M := M)
        g r s i α P)) := by
  have h_clm :=
    ((tensorL2ChartComponentCutoffCLM (I := I) (M := M) g r s
        α P).continuous.tendsto _).comp
      (tensorL2_eigenvectorSmoothApprox_tendsto
        (I := I) (M := M) g r s i)
  simp only [Function.comp_def, tensorL2ChartComponentCutoffCLM_apply] at h_clm
  exact h_clm

theorem tensorCovDerivCrossRight_integral_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (S : SmoothCcTensor g r s) :
    Filter.Tendsto
      (fun n => ∫ x, tensorCovDerivCrossRight (I := I) (M := M) g r s
          (chartAtlasPOU I M α)
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor
          S x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g))
      atTop
      (𝓝 (⟪TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i),
          ((covDerivAlongGrad (I := I) (M := M) g r s S (chartAtlasPOU I M α) :
            SmoothCcTensor g r s) : TensorL2 r s g)⟫_ℝ)) := by
  have h_clm :=
    ((innerSL ℝ
        ((covDerivAlongGrad (I := I) (M := M) g r s S (chartAtlasPOU I M α) :
          SmoothCcTensor g r s) :
          TensorL2 r s g)).continuous.tendsto _).comp
      (tensorL2_eigenvectorSmoothApprox_tendsto
        (I := I) (M := M) g r s i)
  simp only [Function.comp_def, innerSL_apply_apply] at h_clm
  rw [real_inner_comm]
  refine h_clm.congr ?_
  intro n
  rw [tensorCovDerivCrossRight_integral_eq_innerLow (I := I) (M := M) g r s
    (chartAtlasPOU I M α)
    (eigenvectorSmoothApprox (I := I) (M := M) g r s i n).toCcTensor S,
    real_inner_comm]

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

example (S : SmoothCcTensor g r s)
    (V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    SmoothCcTensor g r s :=
  covDerivAlong (I := I) (M := M) g r s S V

example (S : SmoothCcTensor g r s) (ζ : C^∞⟮I, M; ℝ⟯) :
    SmoothCcTensor g r s :=
  covDerivAlongGrad (I := I) (M := M) g r s S ζ

example (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x =
      tensorInnerPointwise (I := I) (M := M) g r s x
        (w.toFun x)
        ((covDerivAlongGrad (I := I) (M := M) g r s S ζ).toFun x) :=
  tensorCovDerivCrossRight_eq_tensorInnerPointwise_grad
    (I := I) (M := M) g r s ζ w S x

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
