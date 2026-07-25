import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorBochner
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FixedFieldThirdOrderCommutator
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivSecondOrderCommutation
import DifferentialGeometry.Geometry.Curvature.Order2Defect.MetricTraceIntertwining
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.PointwiseToL2Packaging
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.MovingFrameGenuineFieldFiberEnergy
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.CovGradBundleEquivFiberNormFrameSum
import DifferentialGeometry.Geometry.Curvature.Order2Defect.MetricTraceFrame
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.FrozenFrameTrace
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.BareSlot0CurryParseval
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.SlotSubstitutionFiberNormBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.NablaTensorCurvSecIdentification
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvatureRS
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedSlotwiseCurvature
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformDiffCurvatureNormBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_succ_eq_sum_slot0Curry_smoothOrthoFrame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 (s + 1) I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T =
      ∑ a : Fin (Module.finrank ℝ E),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (slot0Curry (I := I) (M := M) g x s
            (fun a => smoothOrthoFrame (I := I) g x a x) (fun k : Fin 0 => k.elim0) T a) := by
  classical
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) g x a x with he
  have hn : (Module.finrank ℝ E) = Module.finrank ℝ (TangentSpace I x) := rfl
  have horth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin (Module.finrank ℝ E), ∑ J : Fin s → Fin (Module.finrank ℝ E),
          fiberNormSqSummand (I := I) (M := M) g x 0 s S (Module.finrank ℝ E) e K J := fun S =>
    rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g s x S e hn horth
  have hreprSucc : ∀ S : TensorRSSpace 0 (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x S =
        ∑ K : Fin 0 → Fin (Module.finrank ℝ E), ∑ J : Fin (s + 1) → Fin (Module.finrank ℝ E),
          fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1) S (Module.finrank ℝ E) e K J := fun S =>
    rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g (s + 1) x S e hn horth
  exact riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame (I := I) (M := M) g s x e
    (fun k : Fin 0 => k.elim0) hreprS hreprSucc T

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0S_eq_of_toModel_eq' {t : ℕ} {x : M} {T T' : Tensor0SSpace t I x}
    (h : ∀ v : Fin t → E, Tensor0SSpace.toModel T v = Tensor0SSpace.toModel T' v) : T = T' :=
  Tensor0SSpace.toModel_injective (ContinuousMultilinearMap.ext h)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma tensor00Scalar_unitZeroSec' (x : M) :
    tensor00Scalar (I := I) (M := M) x (unitZeroSec (I := I) (M := M) x) = 1 := by
  rw [tensor00Scalar_apply (I := I) (M := M) x _ (fun k : Fin 0 => k.elim0)]
  rw [show ((unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) : ℝ) =
      Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) (fun k : Fin 0 => k.elim0) from rfl]
  rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.constOfIsEmpty_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma tensor0S_zero_span' (x : M) (τ : Tensor0SSpace 0 I x) :
    τ = tensor00Scalar (I := I) (M := M) x τ • unitZeroSec (I := I) (M := M) x := by
  apply tensor0S_eq_of_toModel_eq' (I := I) (M := M)
  intro v
  rw [show v = (fun k : Fin 0 => k.elim0) from funext (fun k => k.elim0)]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [show Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x)
      (fun k : Fin 0 => k.elim0) = 1 from by
    rw [unitZeroSec_apply (I := I) (M := M) x, Tensor0SSpace.toModel_ofModel,
      ContinuousMultilinearMap.constOfIsEmpty_apply]]
  rw [show Tensor0SSpace.toModel τ (fun k : Fin 0 => k.elim0) =
      tensor00Scalar (I := I) (M := M) x τ from
    (tensor00Scalar_apply (I := I) (M := M) x τ (fun k : Fin 0 => k.elim0)).symm]
  rw [smul_eq_mul, mul_one]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma tensor0SAsRS_unit_recover (t : ℕ) (x : M) (W : TensorRSSpace 0 t I x) :
    tensor0SToTensorRS (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from W)
          (unitZeroSec (I := I) (M := M) x)) = W := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 t x
  intro τ
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SToTensorRS (I := I) (M := M) x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from W)
            (unitZeroSec (I := I) (M := M) x))) τ =
      tensor00Scalar (I := I) (M := M) x τ •
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from W)
          (unitZeroSec (I := I) (M := M) x)) from
    tensor0SAsRS_apply (I := I) (M := M) x _ τ]
  conv_rhs => rw [tensor0S_zero_span' (I := I) (M := M) x τ]
  rw [ContinuousLinearMap.map_smul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma tensor0SAsRS_sub' (t : ℕ) (x : M) (C D : Tensor0SSpace t I x) :
    tensor0SToTensorRS (I := I) (M := M) x (C - D) =
      tensor0SToTensorRS (I := I) (M := M) x C - tensor0SToTensorRS (I := I) (M := M) x D := by
  have h : (tensor0SToTensorRS (I := I) (M := M) x (C - D) :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) =
      (tensor0SToTensorRS (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) -
        (tensor0SToTensorRS (I := I) (M := M) x D :
          Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) := by
    apply ContinuousLinearMap.ext
    intro τ
    change tensor00Scalar (I := I) (M := M) x τ • (C - D) =
      tensor00Scalar (I := I) (M := M) x τ • C - tensor00Scalar (I := I) (M := M) x τ • D
    apply tensor0S_eq_of_toModel_eq' (I := I) (M := M)
    intro v
    rw [Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_sub,
      Tensor0SSpace.toModel_smul, Tensor0SSpace.toModel_smul]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sub_apply,
      smul_eq_mul]
    ring
  exact h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SAsRS_add' (t : ℕ) (x : M) (C D : Tensor0SSpace t I x) :
    tensor0SToTensorRS (I := I) (M := M) x (C + D) =
      tensor0SToTensorRS (I := I) (M := M) x C + tensor0SToTensorRS (I := I) (M := M) x D := by
  have h : (tensor0SToTensorRS (I := I) (M := M) x (C + D) :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) =
      (tensor0SToTensorRS (I := I) (M := M) x C :
        Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) +
        (tensor0SToTensorRS (I := I) (M := M) x D :
          Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) := by
    apply ContinuousLinearMap.ext
    intro τ
    change tensor00Scalar (I := I) (M := M) x τ • (C + D) =
      tensor00Scalar (I := I) (M := M) x τ • C + tensor00Scalar (I := I) (M := M) x τ • D
    rw [smul_add]
  exact h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SAsRS_sum' {ι : Type*} (s_dummy : Finset ι) (t : ℕ) (x : M)
    (C : ι → Tensor0SSpace t I x) :
    tensor0SToTensorRS (I := I) (M := M) x (∑ i ∈ s_dummy, C i) =
      ∑ i ∈ s_dummy, tensor0SToTensorRS (I := I) (M := M) x (C i) := by
  classical
  induction s_dummy using Finset.induction with
  | empty => simp [tensor0SToTensorRS]
  | insert a t' ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      have h : (tensor0SToTensorRS (I := I) (M := M) x (C a + ∑ i ∈ t', C i) :
            Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) =
          (tensor0SToTensorRS (I := I) (M := M) x (C a) :
            Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) +
            (tensor0SToTensorRS (I := I) (M := M) x (∑ i ∈ t', C i) :
              Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x) := by
        apply ContinuousLinearMap.ext
        intro τ
        change tensor00Scalar (I := I) (M := M) x τ • (C a + ∑ i ∈ t', C i) =
          tensor00Scalar (I := I) (M := M) x τ • (C a) +
            tensor00Scalar (I := I) (M := M) x τ • (∑ i ∈ t', C i)
        rw [smul_add]
      exact h

omit [CompactSpace M] [I.Boundaryless] in
private lemma frameSum_secondCovDeriv_pair_eq_riemannSec
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) :
    ∑ i : Fin (Module.finrank ℝ E),
        (tensorSecondCovDeriv (I := I) g 0 s
            (fun y : M => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) y (X y))
            (smoothOrthoFrame (I := I) g x i) (fun y : M => S.toSection y) x +
          tensorSecondCovDeriv (I := I) g 0 s (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) y (X y))
            (fun y : M => S.toSection y) x) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (g.inner x
              ((LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) x (X x))
              (smoothOrthoFrame (I := I) g x j x)) •
            riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x j)
              (smoothOrthoFrame (I := I) g x i) (fun y : M => S.toSection y) x +
        ∑ i : Fin (Module.finrank ℝ E),
          riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) y (X y))
            (fun y : M => S.toSection y) x := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set B : Fin n → Π b : M, TangentSpace I b := fun i => smoothOrthoFrame (I := I) g x i with hB
  set w : Fin n → Π b : M, TangentSpace I b :=
    fun i y => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) y (X y) with hw
  set Sf : Π b : M, TensorRSSpace 0 s I b := fun y => S.toSection y with hSf
  set a : Fin n → Fin n → ℝ :=
    fun i j => g.inner x (w i x) (smoothOrthoFrame (I := I) g x j x) with ha

  have hBsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, B i b⟩ : TotalSpace E (TangentSpace I))) := fun i =>
    smoothOrthoFrame_smooth (I := I) g x i
  have hwsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, w i b⟩ : TotalSpace E (TangentSpace I))) := fun i =>
    covApply_contMDiff (cov := LeviCivita (I := I) g) hX (hBsm i)
  have hBon : ∀ i j : Fin n,
      g.inner x (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j

  have hric : ∀ i : Fin n,
      tensorSecondCovDeriv (I := I) g 0 s (B i) (w i) Sf x -
          tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x =
        riemannSec (tensorCov (I := I) g 0 s) (B i) (w i) Sf x := by
    intro i
    exact tensorSecondCovDeriv_antisymm_eq_riemannSec (I := I) g 0 s Sf
      ((hBsm i x).mdifferentiableAt (by simp)) ((hwsm i x).mdifferentiableAt (by simp))

  have hpair : ∀ i : Fin n,
      tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x +
          tensorSecondCovDeriv (I := I) g 0 s (B i) (w i) Sf x =
        (2 : ℝ) • tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x +
          riemannSec (tensorCov (I := I) g 0 s) (B i) (w i) Sf x := by
    intro i
    have hr := hric i
    rw [two_smul]
    linear_combination (norm := module) hr
  rw [Finset.sum_congr rfl (fun i _ => hpair i)]
  rw [Finset.sum_add_distrib]
  congr 1

  have hfsh : ∀ i : Fin n,
      tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x =
        firstSlotHessMap (I := I) g 0 s (B i) Sf x (w i x) :=
    fun i => tensorSecondCovDeriv_eq_firstSlotHessMap (I := I) g 0 s (w i) (B i) Sf x

  have hexp : ∀ i : Fin n,
      w i x = ∑ j : Fin n, a i j • smoothOrthoFrame (I := I) g x j x := by
    intro i
    have := orthonormal_frame_vector_expansion (I := I) g x (w i x)
      (fun j => smoothOrthoFrame (I := I) g x j x) hBon
    simpa [ha] using this

  have hfsh2 : ∀ i : Fin n,
      tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x =
        ∑ j : Fin n, a i j • firstSlotHessMap (I := I) g 0 s (B i) Sf x
          (smoothOrthoFrame (I := I) g x j x) := by
    intro i
    rw [hfsh i, hexp i, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ContinuousLinearMap.map_smul]

  have hfshread : ∀ i j : Fin n,
      firstSlotHessMap (I := I) g 0 s (B i) Sf x (smoothOrthoFrame (I := I) g x j x) =
        tensorSecondCovDeriv (I := I) g 0 s (B j) (B i) Sf x := by
    intro i j
    rw [tensorSecondCovDeriv_eq_firstSlotHessMap (I := I) g 0 s (B j) (B i) Sf x]

  have hsumT6 : ∑ i : Fin n, tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x =
      ∑ i : Fin n, ∑ j : Fin n,
        a i j • tensorSecondCovDeriv (I := I) g 0 s (B j) (B i) Sf x := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hfsh2 i]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hfshread i j]

  have hskew : ∀ i j : Fin n, a i j = - a j i := by
    intro i j
    simp only [ha, hw]
    rw [smoothOrthoFrame_cov_skew (I := I) g x i j (X x),
      g.symm x (smoothOrthoFrame (I := I) g x i x) _]

  have hricBB : ∀ i j : Fin n,
      tensorSecondCovDeriv (I := I) g 0 s (B j) (B i) Sf x -
          tensorSecondCovDeriv (I := I) g 0 s (B i) (B j) Sf x =
        riemannSec (tensorCov (I := I) g 0 s) (B j) (B i) Sf x := by
    intro i j
    exact tensorSecondCovDeriv_antisymm_eq_riemannSec (I := I) g 0 s Sf
      ((hBsm j x).mdifferentiableAt (by simp)) ((hBsm i x).mdifferentiableAt (by simp))

  have hkey : (2 : ℝ) • (∑ i : Fin n, ∑ j : Fin n,
        a i j • tensorSecondCovDeriv (I := I) g 0 s (B j) (B i) Sf x) =
      ∑ i : Fin n, ∑ j : Fin n,
        a i j • riemannSec (tensorCov (I := I) g 0 s) (B j) (B i) Sf x := by

    have hswap : (∑ i : Fin n, ∑ j : Fin n,
          a i j • tensorSecondCovDeriv (I := I) g 0 s (B i) (B j) Sf x) =
        - ∑ i : Fin n, ∑ j : Fin n,
          a i j • tensorSecondCovDeriv (I := I) g 0 s (B j) (B i) Sf x := by
      have hstep : (∑ i : Fin n, ∑ j : Fin n,
            a i j • tensorSecondCovDeriv (I := I) g 0 s (B i) (B j) Sf x) =
          ∑ i : Fin n, ∑ j : Fin n,
            (- a j i) • tensorSecondCovDeriv (I := I) g 0 s (B i) (B j) Sf x := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hskew i j]
      rw [hstep]
      simp only [neg_smul, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]

    have hdiff : (∑ i : Fin n, ∑ j : Fin n,
          a i j • tensorSecondCovDeriv (I := I) g 0 s (B j) (B i) Sf x) -
        (∑ i : Fin n, ∑ j : Fin n,
          a i j • tensorSecondCovDeriv (I := I) g 0 s (B i) (B j) Sf x) =
        ∑ i : Fin n, ∑ j : Fin n,
          a i j • riemannSec (tensorCov (I := I) g 0 s) (B j) (B i) Sf x := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← smul_sub, hricBB i j]
    rw [← hdiff, hswap, two_smul]
    abel

  rw [show (∑ i : Fin n, (2 : ℝ) • tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x) =
      (2 : ℝ) • ∑ i : Fin n, tensorSecondCovDeriv (I := I) g 0 s (w i) (B i) Sf x from
    (Finset.smul_sum).symm]
  rw [hsumT6, hkey]

omit [NeZero (Module.finrank ℝ E)] in
private lemma covGradBundleEquiv_secondCovDeriv_eq_covGrad_secondCovDerivCc
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) :
    covGradBundleEquiv (I := I) (M := M) 0 s x
        ((tensorCov (I := I) g 0 s).toFun
          (fun y : M => tensorSecondCovDeriv (I := I) g 0 s V V
            (fun z : M => S.toSection z) y) x) =
      (covGrad (I := I) (M := M) g 0 s (secondCovDerivCc (I := I) (M := M) g s hV S)).toSection x := by
  rw [covGrad_toSection_apply (I := I) (M := M) g 0 s
    (secondCovDerivCc (I := I) (M := M) g s hV S) x]
  rfl

private noncomputable def secondCovDerivCommutatorSum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (V X : Π b : M, TangentSpace I b) (x : M) : Tensor0SSpace s I x :=
  (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      riemannSec (tensorCov (I := I) g 0 s) V X
        (covApply (tensorCov (I := I) g 0 s) V (fun y : M => S.toSection y)) x)
      (unitZeroSec (I := I) (M := M) x) +
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      covApply (tensorCov (I := I) g 0 s) V
        (fun y : M => riemannSec (tensorCov (I := I) g 0 s) V X
          (fun z : M => S.toSection z) y) x)
      (unitZeroSec (I := I) (M := M) x) +
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      riemannOp (tensorCov (I := I) g 0 s) x
        ((LeviCivita (I := I) g).toFun X x (V x)) (V x) (S.toSection x))
      (unitZeroSec (I := I) (M := M) x) +
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      riemannOp (tensorCov (I := I) g 0 s) x (X x)
        ((LeviCivita (I := I) g).toFun V x (V x)) (S.toSection x))
      (unitZeroSec (I := I) (M := M) x) -
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
        (riemannOp (LeviCivita (I := I) g) x (V x) (X x) (V x)))
      (unitZeroSec (I := I) (M := M) x) -
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      tensorSecondCovDeriv (I := I) g 0 s
        (fun y : M => (LeviCivita (I := I) g).toFun V y (X y)) V
        (fun y : M => S.toSection y) x)
      (unitZeroSec (I := I) (M := M) x) -
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      tensorSecondCovDeriv (I := I) g 0 s V
        (fun y : M => (LeviCivita (I := I) g).toFun V y (X y))
        (fun y : M => S.toSection y) x)
      (unitZeroSec (I := I) (M := M) x)

omit [NeZero (Module.finrank ℝ E)] in
private lemma slot0Curry_secondCovDeriv_sub_eq_commutatorSum
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {V X : Π b : M, TangentSpace I b}
    (hVs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, V b⟩ : TotalSpace E (TangentSpace I))))
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) :
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            tensorSecondCovDeriv (I := I) g 0 (s + 1) V V
                (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
            (unitZeroSec (I := I) (M := M) x)) (X x) -
        tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (covGrad (I := I) (M := M) g 0 s
              (secondCovDerivCc (I := I) (M := M) g s hVs S)).toSection x)
            (unitZeroSec (I := I) (M := M) x)) (X x) =
      secondCovDerivCommutatorSum (I := I) (M := M) g s S V X x := by
  classical
  apply tensor0S_eq_of_toModel_eq' (I := I) (M := M)
  intro m
  rw [Tensor0SSpace.toModel_sub]
  rw [secondCovDerivCommutatorSum]
  exact secondCovDeriv_covGrad_sub_covGrad_secondCovDeriv_slot0_eq (I := I) g s S hVs hXs x m

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma wrap_carrierSevenInner_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (V X : Π b : M, TangentSpace I b) (x : M) :
    tensor0SToTensorRS (I := I) (M := M) x (secondCovDerivCommutatorSum (I := I) (M := M) g s S V X x) =
      riemannSec (tensorCov (I := I) g 0 s) V X
          (covApply (tensorCov (I := I) g 0 s) V (fun y : M => S.toSection y)) x +
        covApply (tensorCov (I := I) g 0 s) V
          (fun y : M => riemannSec (tensorCov (I := I) g 0 s) V X
            (fun z : M => S.toSection z) y) x +
        riemannOp (tensorCov (I := I) g 0 s) x
          ((LeviCivita (I := I) g).toFun X x (V x)) (V x) (S.toSection x) +
        riemannOp (tensorCov (I := I) g 0 s) x (X x)
          ((LeviCivita (I := I) g).toFun V x (V x)) (S.toSection x) -
        (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
          (riemannOp (LeviCivita (I := I) g) x (V x) (X x) (V x)) -
        tensorSecondCovDeriv (I := I) g 0 s
          (fun y : M => (LeviCivita (I := I) g).toFun V y (X y)) V
          (fun y : M => S.toSection y) x -
        tensorSecondCovDeriv (I := I) g 0 s V
          (fun y : M => (LeviCivita (I := I) g).toFun V y (X y))
          (fun y : M => S.toSection y) x := by
  rw [secondCovDerivCommutatorSum]
  rw [tensor0SAsRS_sub', tensor0SAsRS_sub', tensor0SAsRS_sub',
    tensor0SAsRS_add', tensor0SAsRS_add', tensor0SAsRS_add']
  rw [tensor0SAsRS_unit_recover, tensor0SAsRS_unit_recover, tensor0SAsRS_unit_recover,
    tensor0SAsRS_unit_recover, tensor0SAsRS_unit_recover, tensor0SAsRS_unit_recover,
    tensor0SAsRS_unit_recover]

private lemma slot0_read_curv_eq_sum_carrier
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) :
    tensor0SToTensorRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x)) (X x)) =
      ∑ i : Fin (Module.finrank ℝ E),
        tensor0SToTensorRS (I := I) (M := M) x
          (secondCovDerivCommutatorSum (I := I) (M := M) g s S
            (smoothOrthoFrame (I := I) g x i) X x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn

  set D : Fin n → Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x := fun i =>
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      tensorSecondCovDeriv (I := I) g 0 (s + 1) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x i)
          (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x) -
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g 0 s
        (secondCovDerivCc (I := I) (M := M) g s
          (smoothOrthoFrame_smooth (I := I) g x i) S)).toSection x) with hD

  have hcurv : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) = ∑ i : Fin n, D i := by
    rw [pointwiseTensorCurv_toSection_eq_frame_sum (I := I) (M := M) g s S x]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hD]
    rw [covGradBundleEquiv_secondCovDeriv_eq_covGrad_secondCovDerivCc (I := I) (M := M) g s S
      (smoothOrthoFrame_smooth (I := I) g x i) x]
  rw [hcurv]

  rw [ContinuousLinearMap.sum_apply, map_sum, ContinuousLinearMap.sum_apply,
    tensor0SAsRS_sum']
  refine Finset.sum_congr rfl (fun i _ => ?_)

  rw [hD]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorSecondCovDeriv (I := I) g 0 (s + 1) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g 0 s
            (secondCovDerivCc (I := I) (M := M) g s
              (smoothOrthoFrame_smooth (I := I) g x i) S)).toSection x))
        (unitZeroSec (I := I) (M := M) x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        tensorSecondCovDeriv (I := I) g 0 (s + 1) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (covGrad (I := I) (M := M) g 0 s S).toSection y) x)
        (unitZeroSec (I := I) (M := M) x) -
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (covGrad (I := I) (M := M) g 0 s
          (secondCovDerivCc (I := I) (M := M) g s
            (smoothOrthoFrame_smooth (I := I) g x i) S)).toSection x)
        (unitZeroSec (I := I) (M := M) x) from by
    rw [ContinuousLinearMap.sub_apply]]
  rw [map_sub, ContinuousLinearMap.sub_apply]
  congr 1
  exact slot0Curry_secondCovDeriv_sub_eq_commutatorSum (I := I) (M := M) g s S
    (smoothOrthoFrame_smooth (I := I) g x i) hXs x

omit [CompactSpace M] [I.Boundaryless] in
private lemma frameSum_secondCovDeriv_pair_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) :
    ∑ i : Fin (Module.finrank ℝ E),
        (tensorSecondCovDeriv (I := I) g 0 s
            (fun y : M => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) y (X y))
            (smoothOrthoFrame (I := I) g x i) (fun y : M => S.toSection y) x +
          tensorSecondCovDeriv (I := I) g 0 s (smoothOrthoFrame (I := I) g x i)
            (fun y : M => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) y (X y))
            (fun y : M => S.toSection y) x) = 0 := by
  classical
  rw [frameSum_secondCovDeriv_pair_eq_riemannSec (I := I) (M := M) g s S hX x]
  set n : ℕ := Module.finrank ℝ E with hn
  set B : Fin n → Π b : M, TangentSpace I b := fun i => smoothOrthoFrame (I := I) g x i with hB
  set w : Fin n → Π b : M, TangentSpace I b :=
    fun i y => (LeviCivita (I := I) g).toFun (smoothOrthoFrame (I := I) g x i) y (X y) with hw
  set Sf : Π b : M, TensorRSSpace 0 s I b := fun y => S.toSection y with hSf
  set a : Fin n → Fin n → ℝ :=
    fun i j => g.inner x (w i x) (smoothOrthoFrame (I := I) g x j x) with ha

  have hBsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, B i b⟩ : TotalSpace E (TangentSpace I))) := fun i =>
    smoothOrthoFrame_smooth (I := I) g x i
  have hwsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, w i b⟩ : TotalSpace E (TangentSpace I))) := fun i =>
    covApply_contMDiff (cov := LeviCivita (I := I) g) hX (hBsm i)
  have hBon : ∀ i j : Fin n,
      g.inner x (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x j x) =
        if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j

  have hexp : ∀ i : Fin n, w i x = ∑ j : Fin n, a i j • B j x := by
    intro i
    have := orthonormal_frame_vector_expansion (I := I) g x (w i x)
      (fun j => smoothOrthoFrame (I := I) g x j x) hBon
    simpa [ha, hB] using this

  have hsec_to_op : ∀ Y : Π b : M, TangentSpace I b,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun b : M => (⟨b, Y b⟩ : TotalSpace E (TangentSpace I))) →
      ∀ i : Fin n, riemannSec (tensorCov (I := I) g 0 s) (B i) Y Sf x =
        riemannOp (tensorCov (I := I) g 0 s) x (B i x) (Y x) (Sf x) := by
    intro Y hY i
    exact riemannSec_eq_riemannOp_smooth (cov := tensorCov (I := I) g 0 s)
      (hBsm i) hY S.toSection.contMDiff

  have hfirst : (∑ i : Fin n, ∑ j : Fin n,
        a i j • riemannSec (tensorCov (I := I) g 0 s) (B j) (B i) Sf x) =
      ∑ i : Fin n, ∑ j : Fin n,
        a i j • riemannOp (tensorCov (I := I) g 0 s) x (B j x) (B i x) (Sf x) :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
      rw [hsec_to_op (B i) (hBsm i) j]))

  have hsecond : (∑ i : Fin n,
        riemannSec (tensorCov (I := I) g 0 s) (B i) (w i) Sf x) =
      ∑ i : Fin n, ∑ j : Fin n,
        a i j • riemannOp (tensorCov (I := I) g 0 s) x (B i x) (B j x) (Sf x) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hsec_to_op (w i) (hwsm i) i, hexp i]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply]

  rw [hfirst, hsecond]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [riemannOp_swap (cov := tensorCov (I := I) g 0 s) x (B i x) (B j x)]
  rw [smul_neg]
  abel

lemma slot0_read_curv_eq_frameFree
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    {X : Π b : M, TangentSpace I b}
    (hXs : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, X b⟩ : TotalSpace E (TangentSpace I))))
    (x : M) :
    tensor0SToTensorRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
            (unitZeroSec (I := I) (M := M) x)) (X x)) =
      ∑ i : Fin (Module.finrank ℝ E),
          nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) X
            (fun y : M => S.toSection y) x +
        (2 : ℝ) • ∑ i : Fin (Module.finrank ℝ E),
          riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i) X
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y)) x -
        ∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
            (riemannOp (LeviCivita (I := I) g) x (smoothOrthoFrame (I := I) g x i x) (X x)
              (smoothOrthoFrame (I := I) g x i x)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set B : Fin n → Π b : M, TangentSpace I b := fun i => smoothOrthoFrame (I := I) g x i with hB
  set Sf : Π b : M, TensorRSSpace 0 s I b := fun y => S.toSection y with hSf

  have hBsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, B i b⟩ : TotalSpace E (TangentSpace I))) := fun i =>
    smoothOrthoFrame_smooth (I := I) g x i
  have hBBsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, covApply (LeviCivita (I := I) g) (B i) (B i) b⟩
        : TotalSpace E (TangentSpace I))) := fun i =>
    covApply_contMDiff (cov := LeviCivita (I := I) g) (hBsm i) (hBsm i)
  have hBXsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => (⟨b, covApply (LeviCivita (I := I) g) (B i) X b⟩
        : TotalSpace E (TangentSpace I))) := fun i =>
    covApply_contMDiff (cov := LeviCivita (I := I) g) (hBsm i) hXs

  have hper : ∀ i : Fin n,
      tensor0SToTensorRS (I := I) (M := M) x (secondCovDerivCommutatorSum (I := I) (M := M) g s S (B i) X x) =
        nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s) (B i) (B i) X Sf x +
          (2 : ℝ) • riemannSec (tensorCov (I := I) g 0 s) (B i) X
            (covApply (tensorCov (I := I) g 0 s) (B i) Sf) x -
          (tensorCov (I := I) g 0 s).toFun Sf x
            (riemannOp (LeviCivita (I := I) g) x (B i x) (X x) (B i x)) -
          (tensorSecondCovDeriv (I := I) g 0 s
              (fun y : M => (LeviCivita (I := I) g).toFun (B i) y (X y)) (B i) Sf x +
            tensorSecondCovDeriv (I := I) g 0 s (B i)
              (fun y : M => (LeviCivita (I := I) g).toFun (B i) y (X y)) Sf x) := by
    intro i
    rw [wrap_carrierSevenInner_eq (I := I) (M := M) g s S (B i) X x]

    have hC2eq : covApply (tensorCov (I := I) g 0 s) (B i)
        (fun y : M => riemannSec (tensorCov (I := I) g 0 s) (B i) X Sf y) x =
        nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s) (B i) (B i) X Sf x +
          riemannSec (tensorCov (I := I) g 0 s)
            (covApply (LeviCivita (I := I) g) (B i) (B i)) X Sf x +
          riemannSec (tensorCov (I := I) g 0 s) (B i)
            (covApply (LeviCivita (I := I) g) (B i) X) Sf x +
          riemannSec (tensorCov (I := I) g 0 s) (B i) X
            (covApply (tensorCov (I := I) g 0 s) (B i) Sf) x := by
      have hdef := nablaTensorCurvSec_def (I := I) g (tensorCov (I := I) g 0 s) (B i) (B i) X Sf x
      have hC2_unfold : covApply (tensorCov (I := I) g 0 s) (B i)
          (fun y : M => riemannSec (tensorCov (I := I) g 0 s) (B i) X Sf y) x =
          (tensorCov (I := I) g 0 s).toFun
            (fun b => riemannSec (tensorCov (I := I) g 0 s) (B i) X Sf b) x (B i x) := rfl
      rw [hC2_unfold]
      rw [hdef]
      abel
    rw [hC2eq]

    have hC3op : riemannOp (tensorCov (I := I) g 0 s) x
          ((LeviCivita (I := I) g).toFun X x (B i x)) (B i x) (Sf x) =
        -riemannSec (tensorCov (I := I) g 0 s) (B i)
          (covApply (LeviCivita (I := I) g) (B i) X) Sf x := by
      rw [riemannSec_eq_riemannOp_tensorCov (I := I) g 0 s (hBsm i) (hBXsm i) S.toSection.contMDiff]
      rw [riemannOp_swap (cov := tensorCov (I := I) g 0 s) x (B i x)
        ((covApply (LeviCivita (I := I) g) (B i) X) x), neg_neg]
      rfl

    have hC4op : riemannOp (tensorCov (I := I) g 0 s) x (X x)
          ((LeviCivita (I := I) g).toFun (B i) x (B i x)) (Sf x) =
        -riemannSec (tensorCov (I := I) g 0 s)
          (covApply (LeviCivita (I := I) g) (B i) (B i)) X Sf x := by
      rw [riemannSec_eq_riemannOp_tensorCov (I := I) g 0 s (hBBsm i) hXs S.toSection.contMDiff]
      rw [riemannOp_swap (cov := tensorCov (I := I) g 0 s) x
        ((covApply (LeviCivita (I := I) g) (B i) (B i)) x) (X x), neg_neg]
      rfl
    rw [hC3op, hC4op, two_smul]
    abel

  rw [slot0_read_curv_eq_sum_carrier (I := I) (M := M) g s S hXs x]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hper i)]
  have hC6C7 := frameSum_secondCovDeriv_pair_eq_zero (I := I) (M := M) g s S hXs x

  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [show (∑ i : Fin n,
        (tensorSecondCovDeriv (I := I) g 0 s
            (fun y : M => (LeviCivita (I := I) g).toFun (B i) y (X y)) (B i) Sf x +
          tensorSecondCovDeriv (I := I) g 0 s (B i)
            (fun y : M => (LeviCivita (I := I) g).toFun (B i) y (X y)) Sf x)) = 0 from hC6C7]
  rw [Finset.smul_sum]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma fiberNormSqComponent_eq_toModel_unitEval
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (T : TensorRSSpace 0 s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n) (J : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g x 0 s T n e K₀ J =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T)
          (unitZeroSec (I := I) (M := M) x))
        (fun k => e (J k)) := by
  rw [fiberNormSqComponent]
  have hscal : ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
        (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) =
      unitZeroSec (I := I) (M := M) x := by
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro m
    have hL : Tensor0SSpace.toModel
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K₀ k))) : Tensor0SSpace 0 I x) m = 1 := by
      change ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 0) ℝ).compContinuousLinearMap
          (fun k => g.inner x (e (K₀ k)))) m = 1
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiAlgebra_apply]
      simp
    have hR : Tensor0SSpace.toModel (unitZeroSec (I := I) (M := M) x) m = 1 := by
      rw [unitZeroSec_apply, Tensor0SSpace.toModel_ofModel,
        ContinuousMultilinearMap.constOfIsEmpty_apply]
    rw [hL, hR]
  rw [hscal]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma riemannianFiberNormSq_eq_embedRS_unitEval
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) (T : TensorRSSpace 0 s I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x T =
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (embedRS (I := I) (M := M) x s
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T)
            (unitZeroSec (I := I) (M := M) x))) := by
  classical
  obtain ⟨n, e, _bse, _hn, _hbse, _horth, _hpars, _hexpand, hreprS⟩ :=
    tangent_orthonormalBasisS_witness (I := I) (M := M) g s x
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x s e hreprS T K₀]
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x s e hreprS
    (embedRS (I := I) (M := M) x s
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T)
        (unitZeroSec (I := I) (M := M) x))) K₀]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [fiberNormSqComponent_eq_toModel_unitEval (I := I) (M := M) g x s T e K₀ J]
  rw [fiberNormSqComponent_embedRS (I := I) (M := M) g x s
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T)
      (unitZeroSec (I := I) (M := M) x)) e K₀ J]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma riemannSec_tensorRSCov_unitEval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (τ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        riemannSec (tensorCov (I := I) g 0 s)
          (fun b => X b) (fun b => W b) (fun b => τ b) x)
        (unitZeroSec (I := I) (M := M) x) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (fun b => X b) (fun b => W b)
        (fun b => (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from τ b)
          (unitZeroSec (I := I) (M := M) b)) x := by
  classical
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro u
  have hkey := riemannSec_tensorCov_apply_eval (I := I) (M := M) g 0 s X W τ
    (unitZeroSec (I := I) (M := M)) x u
  have hzero : riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
      (fun b => X b) (fun b => W b)
      (fun b => unitZeroSec (I := I) (M := M) b) x = 0 :=
    riemannSec_tensor0SCov_zero_eq_zero (I := I) g X W
      (fun b => unitZeroSec (I := I) (M := M) b) unitZeroSec.contMDiff x
  rw [hzero, map_zero] at hkey
  have hzeromodel : Tensor0SSpace.toModel (0 : Tensor0SSpace s I x) u = 0 := by simp
  rw [hzeromodel, sub_zero] at hkey
  exact hkey

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma riemannSecRS_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {X Y : Π b : M, TangentSpace I b} {τ : Π b : M, TensorRSSpace 0 s I b}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hτ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y (τ y))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (riemannSec (tensorCov (I := I) g 0 s) X Y τ y)) := by
  have hbr : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (VectorField.mlieBracket I X Y)) :=
    mlieBracket_contMDiff (I := I) hX hY
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s) X
          (covApply (tensorCov (I := I) g 0 s) Y τ) y)) :=
    covApplyRS_contMDiff (I := I) g 0 s (covApplyRS_contMDiff (I := I) g 0 s hτ hY) hX
  have h2 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s) Y
          (covApply (tensorCov (I := I) g 0 s) X τ) y)) :=
    covApplyRS_contMDiff (I := I) g 0 s (covApplyRS_contMDiff (I := I) g 0 s hτ hX) hY
  have h3 : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s) (VectorField.mlieBracket I X Y) τ y)) :=
    covApplyRS_contMDiff (I := I) g 0 s hτ hbr
  have hresult := (h1.sub_section h2).sub_section h3
  refine hresult.congr ?_
  intro b
  rfl

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma nablaTensorCurvSec_tensorRSCov_unitEval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (τ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
          (fun b => X b) (fun b => Y b) (fun b => Z b) (fun b => τ b) x)
        (unitZeroSec (I := I) (M := M) x) =
      nablaTensor0SCurv (I := I) g s X Y Z
        (fun b => (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from τ b)
          (unitZeroSec (I := I) (M := M) b)) x := by
  classical
  set A : Π b : M, Tensor0SSpace s I b :=
    fun b => (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from τ b)
      (unitZeroSec (I := I) (M := M) b) with hA

  have hCovXY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply (LeviCivita (I := I) g)
      (fun b => X b) (fun b => Y b))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Y.contMDiff
  have hCovXZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply (LeviCivita (I := I) g)
      (fun b => X b) (fun b => Z b))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Z.contMDiff
  set covXY : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b)) hCovXY
    with hCovXY_def
  set covXZ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Z b)) hCovXZ
    with hCovXZ_def

  have hcovτ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s) (fun b => X b) (fun b => τ b) y)) :=
    covApplyRS_contMDiff (I := I) g 0 s τ.contMDiff X.contMDiff
  set covτ : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯ :=
    ContMDiffSection.mk (covApply (tensorCov (I := I) g 0 s) (fun b => X b) (fun b => τ b)) hcovτ
    with hcovτ_def

  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (riemannSec (tensorCov (I := I) g 0 s)
          (fun b' => Y b') (fun b' => Z b') (fun b' => τ b') y)) :=
    riemannSecRS_contMDiff (I := I) g s Y.contMDiff Z.contMDiff τ.contMDiff
  set Rsec : Cₛ^∞⟮I; TensorRSModel 0 s ℝ E, (fun y : M => TensorRSSpace 0 s I y)⟯ :=
    ContMDiffSection.mk (fun b => riemannSec (tensorCov (I := I) g 0 s)
      (fun b' => Y b') (fun b' => Z b') (fun b' => τ b') b) hRsec with hRsec_def
  rw [nablaTensorCurvSec_def, nablaTensor0SCurv_def]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]

  refine congrArg₂ HSub.hSub (congrArg₂ HSub.hSub (congrArg₂ HSub.hSub ?_ ?_) ?_) ?_
  · have h1 := covDeriv_unit_eval_eq_genVal (I := I) (M := M) g s Rsec x (X x)
    have hRsec_app : ∀ b, Rsec b = riemannSec (tensorCov (I := I) g 0 s)
        (fun b' => Y b') (fun b' => Z b') (fun b' => τ b') b := fun b => rfl
    simp only [hRsec_app] at h1
    rw [h1]
    have hsec_eq : (fun b => (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from
          riemannSec (tensorCov (I := I) g 0 s)
            (fun b' => Y b') (fun b' => Z b') (fun b' => τ b') b)
          (unitZeroSec (I := I) (M := M) b)) =
        (fun b => riemannSec
          (Tensor0SNabla.tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (fun b' => Y b') (fun b' => Z b')
          (fun b' => (show Tensor0SSpace 0 I b' →L[ℝ] Tensor0SSpace s I b' from τ b')
            (unitZeroSec (I := I) (M := M) b')) b) := by
      funext b
      exact riemannSec_tensorRSCov_unitEval (I := I) (M := M) g s Y Z τ b
    rw [hsec_eq]
  · have h2 := riemannSec_tensorRSCov_unitEval (I := I) (M := M) g s covXY Z τ x
    have hCovXY_app : ∀ b, covXY b = covApply (LeviCivita (I := I) g)
        (fun b' => X b') (fun b' => Y b') b := fun b => rfl
    simp only [hCovXY_app] at h2
    exact h2
  · have h3 := riemannSec_tensorRSCov_unitEval (I := I) (M := M) g s Y covXZ τ x
    have hCovXZ_app : ∀ b, covXZ b = covApply (LeviCivita (I := I) g)
        (fun b' => X b') (fun b' => Z b') b := fun b => rfl
    simp only [hCovXZ_app] at h3
    exact h3
  · have h4 := riemannSec_tensorRSCov_unitEval (I := I) (M := M) g s Y Z covτ x
    have hcovτ_app : ∀ b, covτ b = covApply (tensorCov (I := I) g 0 s)
        (fun b' => X b') (fun b' => τ b') b := fun b => rfl
    simp only [hcovτ_app] at h4
    rw [h4]
    congr 1
    rw [covApply_unit_eval_eq_genVal (I := I) (M := M) g s τ (fun b => X b)]

private theorem exists_frameSummed_nablaTensorCurvSec_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) :
    ∃ Cd : ℕ → ℝ, (∀ s, 0 ≤ Cd s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (a : Fin (Module.finrank ℝ E)),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (∑ i : Fin (Module.finrank ℝ E),
              nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x) ≤
          Cd s * riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
  classical
  obtain ⟨Kw, hKw_nn, hKw⟩ :=
    exists_uniform_nablaCurvSec_LeviCivita_gNorm_bound (I := I) (M := M) g
  refine ⟨fun s => (s : ℝ) ^ 2 * Kw, fun s => by positivity, fun s S x a => ?_⟩

  set B : Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := fun i =>
    ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i) with hB
  set Ba : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothOrthoFrame (I := I) g x a)
      (smoothOrthoFrame_smooth (I := I) g x a) with hBa

  set A : Π b : M, Tensor0SSpace s I b := fun b =>
    (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace s I b from S.toSection b)
      (unitZeroSec (I := I) (M := M) b) with hA
  set W : TangentSpace I x →L[ℝ] TangentSpace I x :=
    nablaBaseSlotCurvFrameSumCLM (I := I) g B Ba x with hW

  set V : TensorRSSpace 0 s I x := ∑ i : Fin (Module.finrank ℝ E),
    nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
      (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x with hV

  have hVunit : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from V)
      (unitZeroSec (I := I) (M := M) x) =
      (- ∑ k : Fin s,
        tensorSlotSubstCLM (I := I) s x (tangentSlotCLM (I := I) s k W) (A x)) := by

    rw [hV]
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          ∑ i : Fin (Module.finrank ℝ E),
            nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x) =
        ∑ i : Fin (Module.finrank ℝ E),
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
              (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x) from rfl]
    rw [ContinuousLinearMap.sum_apply]
    have hper : ∀ i : Fin (Module.finrank ℝ E),
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
            (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x)
          (unitZeroSec (I := I) (M := M) x) =
        nablaTensor0SCurv (I := I) g s (B i) (B i) Ba A x := fun i =>
      nablaTensorCurvSec_tensorRSCov_unitEval (I := I) (M := M) g s (B i) (B i) Ba S.toSection x
    rw [Finset.sum_congr rfl (fun i _ => hper i)]

    apply Tensor0SBundle.Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro u

    rw [show Tensor0SSpace.toModel (∑ i : Fin (Module.finrank ℝ E),
          nablaTensor0SCurv (I := I) g s (B i) (B i) Ba A x) u =
        ∑ i : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel (nablaTensor0SCurv (I := I) g s (B i) (B i) Ba A x) u from by
      rw [← Tensor0SSpace.toModelL_apply (∑ i : Fin (Module.finrank ℝ E),
          nablaTensor0SCurv (I := I) g s (B i) (B i) Ba A x),
        map_sum (Tensor0SSpace.toModelL s x)]
      rw [ContinuousMultilinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Tensor0SSpace.toModelL_apply]]
    rw [frame_sum_nablaTensor0SCurv_diag_baseSlot_eval (I := I) g s Ba A
      (contMDiff_unitEvalSection (I := I) (M := M) g s S) x u]

    have hWuk : ∀ w : TangentSpace I x,
        (∑ i : Fin (Module.finrank ℝ E),
          nablaBaseSlotCurv (I := I) g
            (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame_smooth (I := I) g x i))
            (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame_smooth (I := I) g x i)) Ba x w) = W w := by
      intro w
      rw [hW, nablaBaseSlotCurvFrameSumCLM_apply]
    simp_rw [hWuk]

    rw [show ((fun T : Tensor0SSpace s I x => Tensor0SSpace.toModel T)
          (- ∑ k : Fin s, tensorSlotSubstCLM (I := I) s x
            (tangentSlotCLM (I := I) s k W) (A x))) u =
        Tensor0SSpace.toModel
          (- ∑ k : Fin s, tensorSlotSubstCLM (I := I) s x
            (tangentSlotCLM (I := I) s k W) (A x)) u from rfl]
    rw [Tensor0SSpace.toModel_neg, ContinuousMultilinearMap.neg_apply]
    refine congrArg Neg.neg ?_
    rw [show Tensor0SSpace.toModel (∑ k : Fin s, tensorSlotSubstCLM (I := I) s x
          (tangentSlotCLM (I := I) s k W) (A x))
        = ∑ k : Fin s, Tensor0SSpace.toModel (tensorSlotSubstCLM (I := I) s x
            (tangentSlotCLM (I := I) s k W) (A x)) from by
      rw [← Tensor0SSpace.toModelL_apply (∑ k : Fin s, tensorSlotSubstCLM (I := I) s x
          (tangentSlotCLM (I := I) s k W) (A x)),
        map_sum (Tensor0SSpace.toModelL s x)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Tensor0SSpace.toModelL_apply]]
    rw [ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [toModel_tensorSlotSubstCLM_apply (I := I) s x k W (A x) u]

  rw [riemannianFiberNormSq_eq_embedRS_unitEval (I := I) (M := M) g x s V]
  rw [hVunit]

  have hSrhs : riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (embedRS (I := I) (M := M) x s (A x)) := by
    rw [riemannianFiberNormSq_eq_embedRS_unitEval (I := I) (M := M) g x s (S.toSection x)]
  rw [hSrhs]

  exact riemannianFiberNormSq_slotSub_le (I := I) (M := M) g x s (A x) W Kw hKw_nn
    (fun u => hKw x a u)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma metric_inner_self_nonneg' (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) : 0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with hv0 | hv0
  · rw [hv0]; simp
  · exact (g.pos x v hv0).le

omit [NeZero (Module.finrank ℝ E)] in
private lemma riemannianFiberNormSq_tensorCovDerivAt_frame_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hreprS : ∀ U : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x U =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s U n e K J)
    (hreprSucc : ∀ U : TensorRSSpace 0 (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x U =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (s + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1) U n e K J)
    (j : Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (e j)) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  classical

  have hslice : slot0Curry (I := I) (M := M) g x s e K₀
        ((covGrad (I := I) (M := M) g 0 s S).toSection x) j =
      (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (e j) := by
    rw [slot0Curry_eq_tensor0SToTensorRS_curry_unitZeroSec (I := I) (M := M) g x s e K₀
      ((covGrad (I := I) (M := M) g 0 s S).toSection x) j]
    rw [curry_covGrad_unit_eval_general (I := I) (M := M) g s S x (e j)]
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g 0 s S x (e j))
          (unitZeroSec (I := I) (M := M) x) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (e j))
          (unitZeroSec (I := I) (M := M) x) from rfl]
    exact tensor0SAsRS_unit_recover (I := I) (M := M) s x
      ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (e j))
  rw [← hslice]
  exact riemannianFiberNormSq_slot0Curry_le_of_frame (I := I) (M := M) g s x e K₀
    hreprS hreprSucc ((covGrad (I := I) (M := M) g 0 s S).toSection x) j

private lemma riemannianFiberNormSq_tensorCovDerivAt_direction_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (w : TangentSpace I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x w) ≤
      (Module.finrank ℝ E : ℝ) * g.inner x w w *
        riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  classical
  obtain ⟨n, e, _bse, hn, _hbse, horth, hpars, hexpand, hreprS⟩ :=
    tangent_orthonormalBasisS_witness (I := I) (M := M) g s x
  obtain ⟨n', e', _bse', hn', _hbse', _horth', _hpars', _hexpand', hreprSucc'⟩ :=
    tangent_orthonormalBasisS_witness (I := I) (M := M) g (s + 1) x

  have hreprSucc : ∀ U : TensorRSSpace 0 (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x U =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (s + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1) U n e K J := fun U =>
    rfns_eq_sum_fiberNormSqSummand_of_orthoFrame (I := I) (M := M) g (s + 1) x U e hn horth
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  set grad : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hgrad
  have hgrad_nn : 0 ≤ grad := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _

  set Tj : Fin n → TensorRSSpace 0 s I x := fun j =>
    (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (e j) with hTj
  have hTw : (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x w =
      ∑ j : Fin n, g.inner x (e j) w • Tj j := by
    conv_lhs => rw [hexpand w]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ContinuousLinearMap.map_smul, hTj]

  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x s e hreprS _ K₀]
  rw [hTw]

  have hcomp : ∀ J : Fin s → Fin n,
      fiberNormSqComponent (I := I) (M := M) g x 0 s
          (∑ j : Fin n, g.inner x (e j) w • Tj j) n e K₀ J =
        ∑ j : Fin n, g.inner x (e j) w *
          fiberNormSqComponent (I := I) (M := M) g x 0 s (Tj j) n e K₀ J := by
    intro J
    rw [fiberNormSqComponent_sum (I := I) (M := M) g x 0 s Finset.univ
      (fun j => g.inner x (e j) w • Tj j) n e K₀ J]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [fiberNormSqComponent_smul (I := I) (M := M) g x 0 s (g.inner x (e j) w) (Tj j) n e K₀ J]

  have hCS : ∀ J : Fin s → Fin n,
      (fiberNormSqComponent (I := I) (M := M) g x 0 s
          (∑ j : Fin n, g.inner x (e j) w • Tj j) n e K₀ J) ^ 2 ≤
        g.inner x w w *
          ∑ j : Fin n, (fiberNormSqComponent (I := I) (M := M) g x 0 s (Tj j) n e K₀ J) ^ 2 := by
    intro J
    rw [hcomp J]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) (Finset.univ : Finset (Fin n))
      (fun j => g.inner x (e j) w)
      (fun j => fiberNormSqComponent (I := I) (M := M) g x 0 s (Tj j) n e K₀ J)
    calc (∑ j : Fin n, g.inner x (e j) w *
            fiberNormSqComponent (I := I) (M := M) g x 0 s (Tj j) n e K₀ J) ^ 2
        ≤ (∑ j : Fin n, g.inner x (e j) w ^ 2) *
            ∑ j : Fin n, fiberNormSqComponent (I := I) (M := M) g x 0 s (Tj j) n e K₀ J ^ 2 := hcs
      _ = g.inner x w w *
            ∑ j : Fin n, (fiberNormSqComponent (I := I) (M := M) g x 0 s (Tj j) n e K₀ J) ^ 2 := by
            rw [hpars w]

  calc (∑ J : Fin s → Fin n,
          (fiberNormSqComponent (I := I) (M := M) g x 0 s
            (∑ j : Fin n, g.inner x (e j) w • Tj j) n e K₀ J) ^ 2)
      ≤ ∑ J : Fin s → Fin n, g.inner x w w *
          ∑ j : Fin n, (fiberNormSqComponent (I := I) (M := M) g x 0 s (Tj j) n e K₀ J) ^ 2 :=
        Finset.sum_le_sum (fun J _ => hCS J)
    _ = g.inner x w w *
          ∑ j : Fin n, riemannianFiberNormSq (I := I) (M := M) g 0 s x (Tj j) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x s e hreprS (Tj j) K₀]
    _ ≤ g.inner x w w * ∑ _j : Fin n, grad := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => ?_))
          (metric_inner_self_nonneg' (I := I) (M := M) g x w)
        rw [hTj]
        exact riemannianFiberNormSq_tensorCovDerivAt_frame_le (I := I) (M := M) g s S x e K₀ hreprS hreprSucc j
    _ = (Module.finrank ℝ E : ℝ) * g.inner x w w * grad := by
        have hnE : (n : ℝ) = (Module.finrank ℝ E : ℝ) := by
          rw [hn]; rfl
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hnE]
        ring

private theorem exists_frameSummed_curvDirCovDeriv_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) :
    ∃ Cc : ℕ → ℝ, (∀ s, 0 ≤ Cc s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (a : Fin (Module.finrank ℝ E)),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (∑ i : Fin (Module.finrank ℝ E),
              (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
                (riemannOp (LeviCivita (I := I) g) x (smoothOrthoFrame (I := I) g x i x)
                  (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x i x))) ≤
          Cc s * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) := by
  classical

  obtain ⟨Kbase, hKbase_nn, hKbase⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) g
  set n : ℕ := Module.finrank ℝ E with hn
  refine ⟨fun _ => (n : ℝ) * ((n : ℝ) * (n : ℝ) * Kbase),
    fun _ => by positivity, fun s S x a => ?_⟩
  set grad : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hgrad
  have hgrad_nn : 0 ≤ grad := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _

  set w : Fin n → TangentSpace I x := fun i =>
    riemannOp (LeviCivita (I := I) g) x (smoothOrthoFrame (I := I) g x i x)
      (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x i x) with hw
  set F : Fin n → TensorRSSpace 0 s I x := fun i =>
    (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x (w i) with hF
  have hgB : ∀ i : Fin n, g.inner x (smoothOrthoFrame (I := I) g x i x)
      (smoothOrthoFrame (I := I) g x i x) = 1 := by
    intro i
    have := smoothOrthoFrame_orthonormal_at_center (I := I) g x i i; rwa [if_pos rfl] at this
  have hga : g.inner x (smoothOrthoFrame (I := I) g x a x)
      (smoothOrthoFrame (I := I) g x a x) = 1 := by
    have := smoothOrthoFrame_orthonormal_at_center (I := I) g x a a; rwa [if_pos rfl] at this
  have hw_bd : ∀ i : Fin n, g.inner x (w i) (w i) ≤ Kbase := by
    intro i
    have h := hKbase x (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x a x)
      (smoothOrthoFrame (I := I) g x i x)
    rw [hgB i, hga, mul_one, mul_one, mul_one] at h
    rw [hw]
    exact h

  have hper : ∀ i : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (F i) ≤ (n : ℝ) * Kbase * grad := by
    intro i
    rw [hF]
    refine le_trans (riemannianFiberNormSq_tensorCovDerivAt_direction_le (I := I) (M := M) g s S x (w i)) ?_
    rw [← hn]
    have hwi_nn : 0 ≤ g.inner x (w i) (w i) := metric_inner_self_nonneg' (I := I) (M := M) g x (w i)
    have hstep : (n : ℝ) * g.inner x (w i) (w i) * grad ≤ (n : ℝ) * Kbase * grad := by
      have hle : (n : ℝ) * g.inner x (w i) (w i) ≤ (n : ℝ) * Kbase :=
        mul_le_mul_of_nonneg_left (hw_bd i) (Nat.cast_nonneg n)
      exact mul_le_mul_of_nonneg_right hle hgrad_nn
    exact hstep

  calc riemannianFiberNormSq (I := I) (M := M) g 0 s x (∑ i : Fin n, F i)
      ≤ (n : ℝ) * ∑ i : Fin n, riemannianFiberNormSq (I := I) (M := M) g 0 s x (F i) := by
        have := riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 s x
          (Finset.univ : Finset (Fin n)) F
        rwa [Finset.card_univ, Fintype.card_fin] at this
    _ ≤ (n : ℝ) * ∑ _i : Fin n, ((n : ℝ) * Kbase * grad) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hper i)) (Nat.cast_nonneg n)
    _ = (n : ℝ) * ((n : ℝ) * (n : ℝ) * Kbase) * grad := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

omit [CompactSpace M] [I.Boundaryless] in
private lemma frameSummed_riemannSec_eq_genuineCurvTraceFixedFramePureR
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    (∑ i : Fin (Module.finrank ℝ E),
        riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x a)
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y)) x) =
      genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s
        (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g x a x))
        (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x := by
  classical
  rw [genuineCurvTraceFixedFramePureR_def (I := I) g s
    (smoothExtensionTangent (I := I) x (smoothOrthoFrame (I := I) g x a x))
    (smoothOrthoFrame (I := I) g x) (fun y : M => S.toSection y) x]
  refine Finset.sum_congr rfl (fun i _ => ?_)

  have hcov_sm : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) y
        (covApply (tensorCov (I := I) g 0 s)
          (smoothOrthoFrame (I := I) g x i) (fun y : M => S.toSection y) y)) :=
    covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff
      (smoothOrthoFrame_smooth (I := I) g x i)
  rw [riemannSec_eq_riemannOp_tensorCov (I := I) g 0 s (smoothOrthoFrame_smooth (I := I) g x i)
    (smoothOrthoFrame_smooth (I := I) g x a) hcov_sm]
  rw [riemannSec_eq_riemannOp_tensorCov (I := I) g 0 s (smoothOrthoFrame_smooth (I := I) g x i)
    (smoothExtensionTangent_contMDiff (I := I) x (smoothOrthoFrame (I := I) g x a x)) hcov_sm]
  rw [smoothExtensionTangent_eq (I := I) x (smoothOrthoFrame (I := I) g x a x)]

private lemma pointwiseTensorCurv_fiberNormSq_squared_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (Kpure Cd Cc : ℕ → ℝ)
    (hKpure : ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (v : TangentSpace I x),
        g.inner x v v = 1 →
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (genuineCurvTraceFixedFrameCurvatureOnly (I := I) g s
              (smoothExtensionTangent (I := I) x v) (smoothOrthoFrame (I := I) g x)
              (fun y : M => S.toSection y) x) ≤
          Kpure s *
            riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x))
    (hCd : ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (a : Fin (Module.finrank ℝ E)),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (∑ i : Fin (Module.finrank ℝ E),
              nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
                (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
                (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x) ≤
          Cd s * riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x))
    (hCc : ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) (a : Fin (Module.finrank ℝ E)),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (∑ i : Fin (Module.finrank ℝ E),
              (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
                (riemannOp (LeviCivita (I := I) g) x (smoothOrthoFrame (I := I) g x i x)
                  (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x i x))) ≤
          Cc s * riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x)) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
        ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) ≤
      (Module.finrank ℝ E : ℝ) * (16 * Kpure s + 2 * Cc s) *
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x) +
        (Module.finrank ℝ E : ℝ) * (4 * Cd s) *
          riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn
  set grad : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hgrad
  set base : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hbase
  have hgrad_nn : 0 ≤ grad := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hbase_nn : 0 ≤ base := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _

  have hentry := riemannianFiberNormSq_succ_eq_sum_slot0Curry_smoothOrthoFrame (I := I) (M := M) g s x
    ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)
  rw [hentry]

  set sliceVal : Fin n → TensorRSSpace 0 s I x := fun a =>
    ∑ i : Fin n,
        nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x +
      (2 : ℝ) • ∑ i : Fin n,
          riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x a)
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y)) x -
        ∑ i : Fin n,
          (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
            (riemannOp (LeviCivita (I := I) g) x (smoothOrthoFrame (I := I) g x i x)
              (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x i x)) with hsliceVal
  have hslice_eq : ∀ a : Fin n,
      slot0Curry (I := I) (M := M) g x s (fun a => smoothOrthoFrame (I := I) g x a x)
          (fun k : Fin 0 => k.elim0)
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x) a =
        sliceVal a := by
    intro a
    rw [slot0Curry_eq_tensor0SToTensorRS_curry_unitZeroSec (I := I) (M := M) g x s
      (fun a => smoothOrthoFrame (I := I) g x a x) (fun k : Fin 0 => k.elim0) _ a]
    rw [hsliceVal]
    exact slot0_read_curv_eq_frameFree (I := I) (M := M) g s S
      (smoothOrthoFrame_smooth (I := I) g x a) x
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => by rw [hslice_eq a])]

  have hper : ∀ a : Fin n,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x (sliceVal a) ≤
        (16 * Kpure s + 2 * Cc s) * grad + (4 * Cd s) * base := by
    intro a
    set A_a : TensorRSSpace 0 s I x := ∑ i : Fin n,
        nablaTensorCurvSec (I := I) g (tensorCov (I := I) g 0 s)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x a) (fun y : M => S.toSection y) x with hA_a
    set R_a : TensorRSSpace 0 s I x := ∑ i : Fin n,
        riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
          (smoothOrthoFrame (I := I) g x a)
          (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (fun y : M => S.toSection y)) x with hR_a
    set C5_a : TensorRSSpace 0 s I x := ∑ i : Fin n,
        (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
          (riemannOp (LeviCivita (I := I) g) x (smoothOrthoFrame (I := I) g x i x)
            (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x i x)) with hC5_a
    have hsliceVal_a : sliceVal a = A_a + (2 : ℝ) • R_a - C5_a := by
      rw [hsliceVal, hA_a, hR_a, hC5_a]

    have hbd_A : riemannianFiberNormSq (I := I) (M := M) g 0 s x A_a ≤ Cd s * base := by
      rw [hA_a, hbase]; exact hCd s S x a
    have hbd_C5 : riemannianFiberNormSq (I := I) (M := M) g 0 s x C5_a ≤ Cc s * grad := by
      rw [hC5_a, hgrad]; exact hCc s S x a
    have hbd_R : riemannianFiberNormSq (I := I) (M := M) g 0 s x R_a ≤ Kpure s * grad := by
      rw [hR_a, frameSummed_riemannSec_eq_genuineCurvTraceFixedFramePureR (I := I) (M := M) g s S x a, hgrad]
      exact hKpure s S x (smoothOrthoFrame (I := I) g x a x)
        (by
          have := smoothOrthoFrame_orthonormal_at_center (I := I) g x a a
          simpa using this)
    have hbd_2R : riemannianFiberNormSq (I := I) (M := M) g 0 s x ((2 : ℝ) • R_a) ≤
        4 * (Kpure s * grad) := by
      rw [two_smul]
      calc riemannianFiberNormSq (I := I) (M := M) g 0 s x (R_a + R_a)
          ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x R_a +
              2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x R_a :=
            riemannianFiberNormSq_add_le (I := I) (M := M) g 0 s x R_a R_a
        _ ≤ 2 * (Kpure s * grad) + 2 * (Kpure s * grad) := by
            have := hbd_R; linarith
        _ = 4 * (Kpure s * grad) := by ring

    rw [hsliceVal_a]
    calc riemannianFiberNormSq (I := I) (M := M) g 0 s x (A_a + (2 : ℝ) • R_a - C5_a)
        ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x (A_a + (2 : ℝ) • R_a) +
            2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x C5_a :=
          riemannianFiberNormSq_sub_le (I := I) (M := M) g 0 s x (A_a + (2 : ℝ) • R_a) C5_a
      _ ≤ 2 * (2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x A_a +
              2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x ((2 : ℝ) • R_a)) +
            2 * riemannianFiberNormSq (I := I) (M := M) g 0 s x C5_a := by
          have := riemannianFiberNormSq_add_le (I := I) (M := M) g 0 s x A_a ((2 : ℝ) • R_a)
          linarith
      _ ≤ 2 * (2 * (Cd s * base) + 2 * (4 * (Kpure s * grad))) + 2 * (Cc s * grad) := by
          have h1 := hbd_A; have h2 := hbd_2R; have h3 := hbd_C5; linarith
      _ = (16 * Kpure s + 2 * Cc s) * grad + (4 * Cd s) * base := by ring

  calc (∑ a : Fin n, riemannianFiberNormSq (I := I) (M := M) g 0 s x (sliceVal a))
      ≤ ∑ _a : Fin n, ((16 * Kpure s + 2 * Cc s) * grad + (4 * Cd s) * base) :=
        Finset.sum_le_sum (fun a _ => hper a)
    _ = (n : ℝ) * ((16 * Kpure s + 2 * Cc s) * grad + (4 * Cd s) * base) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (Module.finrank ℝ E : ℝ) * (16 * Kpure s + 2 * Cc s) * grad +
          (Module.finrank ℝ E : ℝ) * (4 * Cd s) * base := by rw [hn]; ring

theorem pointwiseTensorCurv_fiberNormSq_le_first_order
    (g : SmoothRiemannianMetric I M) :
    ∃ K_R K_dR : ℕ → ℝ, (∀ s, 0 ≤ K_R s) ∧ (∀ s, 0 ≤ K_dR s) ∧
      ∀ (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M),
        Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)) ≤
          K_R s * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x)) +
            K_dR s * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x
              (S.toSection x)) := by
  classical

  have hsqrt_add : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    intro a b ha hb
    have h_sum_nn : 0 ≤ a + b := add_nonneg ha hb
    have h_sum_sq_nn : 0 ≤ Real.sqrt a + Real.sqrt b :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h_lhs_sq : Real.sqrt (a + b) ^ 2 = a + b := Real.sq_sqrt h_sum_nn
    have h_rhs_sq : (Real.sqrt a + Real.sqrt b) ^ 2 =
        a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
      rw [add_pow_two, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
    have h_cross_nn : 0 ≤ 2 * (Real.sqrt a * Real.sqrt b) := by positivity
    have h_sq_le : Real.sqrt (a + b) ^ 2 ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
      rw [h_lhs_sq, h_rhs_sq]; linarith
    exact (abs_le_of_sq_le_sq' h_sq_le h_sum_sq_nn).2

  obtain ⟨Kpure, hKpure_nn, hKpure_bd⟩ :=
    exists_uniform_genuineCurvTracePureR_fiberNormSq_bound (I := I) (M := M) g
  obtain ⟨Cd, hCd_nn, hCd_bd⟩ :=
    exists_frameSummed_nablaTensorCurvSec_fiberNormSq_le (I := I) (M := M) g
  obtain ⟨Cc, hCc_nn, hCc_bd⟩ :=
    exists_frameSummed_curvDirCovDeriv_fiberNormSq_le (I := I) (M := M) g

  set nR : ℝ := (Module.finrank ℝ E : ℝ) with hnR
  have hnR_nn : 0 ≤ nR := Nat.cast_nonneg _
  refine ⟨fun s => Real.sqrt (nR * (16 * Kpure s + 2 * Cc s)),
    fun s => Real.sqrt (nR * (4 * Cd s)),
    fun s => Real.sqrt_nonneg _, fun s => Real.sqrt_nonneg _, ?_⟩
  intro s S x

  set Curv : TensorRSSpace 0 (s + 1) I x :=
    (pointwiseTensorCurv (I := I) (M := M) g s S).toSection x with hCurv
  set grad : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
    ((covGrad (I := I) (M := M) g 0 s S).toSection x) with hgrad
  set base : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 s x (S.toSection x) with hbase
  have hgrad_nn : 0 ≤ grad := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (s + 1) x _
  have hbase_nn : 0 ≤ base := riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _

  have hsq : riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x Curv ≤
      nR * (16 * Kpure s + 2 * Cc s) * grad + nR * (4 * Cd s) * base := by
    exact pointwiseTensorCurv_fiberNormSq_squared_bound (I := I) (M := M) g s S x
      Kpure Cd Cc hKpure_bd hCd_bd hCc_bd

  have hPcoef_nn : 0 ≤ nR * (16 * Kpure s + 2 * Cc s) := by
    have := hKpure_nn s; have := hCc_nn s
    have : 0 ≤ 16 * Kpure s + 2 * Cc s := by nlinarith [hKpure_nn s, hCc_nn s]
    exact mul_nonneg hnR_nn this
  have hQcoef_nn : 0 ≤ nR * (4 * Cd s) := mul_nonneg hnR_nn (by nlinarith [hCd_nn s])

  calc Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x Curv)
      ≤ Real.sqrt (nR * (16 * Kpure s + 2 * Cc s) * grad + nR * (4 * Cd s) * base) :=
        Real.sqrt_le_sqrt hsq
    _ ≤ Real.sqrt (nR * (16 * Kpure s + 2 * Cc s) * grad) +
          Real.sqrt (nR * (4 * Cd s) * base) :=
        hsqrt_add _ _ (mul_nonneg hPcoef_nn hgrad_nn) (mul_nonneg hQcoef_nn hbase_nn)
    _ = Real.sqrt (nR * (16 * Kpure s + 2 * Cc s)) * Real.sqrt grad +
          Real.sqrt (nR * (4 * Cd s)) * Real.sqrt base := by
        rw [Real.sqrt_mul hPcoef_nn grad, Real.sqrt_mul hQcoef_nn base]

theorem exists_pointwiseTensorCurv_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    ∃ K_R K_dR : ℝ, 0 ≤ K_R ∧ 0 ≤ K_dR ∧ ∀ (S : SmoothCcTensor g 0 s) (x : M),
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
          ((pointwiseTensorCurv (I := I) (M := M) g s S).toSection x)) ≤
        K_R * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x
            ((covGrad (I := I) (M := M) g 0 s S).toSection x)) +
          K_dR * Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (S.toSection x)) := by
  obtain ⟨K_R, K_dR, hK_R_nn, hK_dR_nn, hbound⟩ :=
    pointwiseTensorCurv_fiberNormSq_le_first_order (I := I) (M := M) g
  exact ⟨K_R s, K_dR s, hK_R_nn s, hK_dR_nn s, fun S x => hbound s S x⟩

end Connection
end Integral
end DifferentialGeometry

end
