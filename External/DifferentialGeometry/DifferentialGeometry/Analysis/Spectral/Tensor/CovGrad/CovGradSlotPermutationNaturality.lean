import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Metric.PointwiseInner.SlotPermutation
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Tensor0SRSCovariantDerivativeAgreement
import Mathlib.GroupTheory.Perm.Fin


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def unitTensor (x : M) : Tensor0SSpace 0 I x :=
  Tensor0SSpace.ofModel
    (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))

def unitModel (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) : Tensor0SModel s ℝ E :=
  Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x)
      (unitTensor (I := I) (M := M) x))

end NormedSpaceModel

section NormedSpaceModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private def covDerivUnitModel (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) (v : TangentSpace I x) : Tensor0SModel s ℝ E :=
  Tensor0SSpace.toModel
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      tensorCovDerivAt (I := I) (M := M) g 0 s W x v)
      (unitTensor (I := I) (M := M) x))

private def unitEvalSection (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) : Π y : M, Tensor0SSpace s I y :=
  fun y =>
    (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace s I y from W.toSection y)
      (unitTensor (I := I) (M := M) y)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma covDerivUnitModel_eq_tensor0SCovariantDerivative
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) (v : TangentSpace I x) :
    covDerivUnitModel (I := I) (M := M) g s W x v =
      Tensor0SSpace.toModel
        (Tensor0SNabla.tensor0SCovariantDerivative I M s
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g)
          (unitEvalSection (I := I) (M := M) g s W) x v) := by
  rw [covDerivUnitModel, tensorCovDerivAt_def]
  congr 1
  exact tensorRSCovariantDerivative_zeroS_unit_eval
    (I := I) (M := M) g s W.toSection x v

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SChartE_section_repr_apply_tuple
    (s : ℕ) (α : M) (T : Π b : M, Tensor0SSpace s I b) (b : M)
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v : Fin s → E) :
    DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr (I := I) s α T b v =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I b) ℝ from T b)
        (fun i => (trivializationAt E (TangentSpace I) α).symmL ℝ b (v i)) := by
  classical
  rw [DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr_apply]
  set e := trivializationAt (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace s I y) α with he
  have hbE : b ∈ e.baseSet := hb
  rw [e.continuousLinearMapAt_apply ℝ, e.coe_linearMapAt_of_mem hbE]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SChartE_section_repr_domDomCongr
    (s : ℕ) (σ : Equiv.Perm (Fin s)) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) :
    DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr (I := I) s α
        (fun y => ContinuousMultilinearMap.domDomCongr σ
          (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I y) ℝ from T y)) b =
      ContinuousMultilinearMap.domDomCongr σ
        (DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr (I := I) s α T b) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro v
  by_cases hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet
  · rw [tensor0SChartE_section_repr_apply_tuple (I := I) s α _ b hb v,
      ContinuousMultilinearMap.domDomCongr_apply,
      ContinuousMultilinearMap.domDomCongr_apply,
      tensor0SChartE_section_repr_apply_tuple (I := I) s α T b hb (fun i => v (σ i))]
  · set e := trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α with he
    have hbE : b ∉ e.baseSet := hb
    rw [DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr_apply,
      e.continuousLinearMapAt_apply ℝ, e.linearMapAt_def_of_notMem hbE]
    rw [ContinuousMultilinearMap.domDomCongr_apply,
      DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr_apply,
      e.continuousLinearMapAt_apply ℝ, e.linearMapAt_def_of_notMem hbE]
    simp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SChartFiberFromModel_apply_tuple
    (s : ℕ) (α : M) (b : M)
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (M0 : Tensor0SModel s ℝ E) (v : Fin s → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I b) ℝ from
        DifferentialGeometry.Integral.Connection.tensor0SChartFiberFromModel (I := I) s α b M0) v =
      M0 (fun i => (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b (v i)) := by
  classical
  have h := Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap (𝕜 := ℝ)
    (F := E) (E := TangentSpace I) (s := s) α b hb M0
  have h2 := DFunLike.congr_fun h v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply] at h2
  exact h2

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SChartFiberFromModel_domDomCongr
    (s : ℕ) (σ : Equiv.Perm (Fin s)) (α : M) (b : M)
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (M0 : Tensor0SModel s ℝ E) :
    DifferentialGeometry.Integral.Connection.tensor0SChartFiberFromModel (I := I) s α b
        (ContinuousMultilinearMap.domDomCongr σ M0) =
      ContinuousMultilinearMap.domDomCongr σ
        (DifferentialGeometry.Integral.Connection.tensor0SChartFiberFromModel (I := I) s α b M0) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro v
  rw [tensor0SChartFiberFromModel_apply_tuple (I := I) s α b hb (ContinuousMultilinearMap.domDomCongr σ M0) v]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [tensor0SChartFiberFromModel_apply_tuple (I := I) s α b hb M0 (fun i => v (σ i))]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0SIntrinsicChartCLM_domDomCongr
    (s : ℕ) (σ : Equiv.Perm (Fin s)) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M)
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v : TangentSpace I b) :
    DifferentialGeometry.Integral.Connection.tensor0SIntrinsicChartCLM (I := I) s α
        (fun y => ContinuousMultilinearMap.domDomCongr σ
          (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I y) ℝ from T y)) b v =
      ContinuousMultilinearMap.domDomCongr σ
        (DifferentialGeometry.Integral.Connection.tensor0SIntrinsicChartCLM (I := I) s α T b v) := by
  classical
  rw [DifferentialGeometry.Integral.Connection.tensor0SIntrinsicChartCLM_apply,
    DifferentialGeometry.Integral.Connection.tensor0SIntrinsicChartCLM_apply]

  set L : Tensor0SModel s ℝ E ≃L[ℝ] Tensor0SModel s ℝ E :=
    (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ σ).toContinuousLinearEquiv with hL
  have hpull :
      (DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr (I := I) s α
          (fun y => ContinuousMultilinearMap.domDomCongr σ
            (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I y) ℝ from T y)) ∘
        (extChartAt I α).symm) =
      (⇑L) ∘
        (DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr (I := I) s α T ∘
          (extChartAt I α).symm) := by
    funext z
    simp only [Function.comp_apply]
    rw [tensor0SChartE_section_repr_domDomCongr (I := I) s σ α T ((extChartAt I α).symm z)]
    rw [hL, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rfl
  rw [hpull]
  rw [L.comp_fderiv]
  rw [ContinuousLinearMap.comp_apply]
  rw [hL, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]

  rw [show (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ σ)
        ((fderiv ℝ (DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr
            (I := I) s α T ∘ (extChartAt I α).symm) (extChartAt I α b))
          (DifferentialGeometry.Integral.Connection.trivToE (I := I) α b v)) =
      ContinuousMultilinearMap.domDomCongr σ
        ((fderiv ℝ (DifferentialGeometry.Integral.Connection.tensor0SChartE_section_repr
            (I := I) s α T ∘ (extChartAt I α).symm) (extChartAt I α b))
          (DifferentialGeometry.Integral.Connection.trivToE (I := I) α b v)) from rfl]

  rw [tensor0SChartFiberFromModel_domDomCongr (I := I) s σ α b hb]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma localSlotCLM_comp_perm
    (s : ℕ) (σ : Equiv.Perm (Fin s)) {b : M} (k : Fin s)
    (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) (i : Fin s) :
    DifferentialGeometry.Integral.Connection.localSlotCLM s k Φ (σ i) =
      DifferentialGeometry.Integral.Connection.localSlotCLM s (σ.symm k) Φ i := by
  by_cases hi : i = σ.symm k
  · subst hi
    rw [Equiv.apply_symm_apply,
      DifferentialGeometry.Integral.Connection.localSlotCLM_self,
      DifferentialGeometry.Integral.Connection.localSlotCLM_self]
  · rw [DifferentialGeometry.Integral.Connection.localSlotCLM_other s k Φ
        (by intro h; exact hi (by rw [← Equiv.symm_apply_apply σ i, h])),
      DifferentialGeometry.Integral.Connection.localSlotCLM_other s (σ.symm k) Φ hi]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartTensor0SSlotCorrection_sum_domDomCongr
    (s : ℕ) (g : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin s)) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (X : Π b : M, TangentSpace I b) (b : M) :
    ∑ k : Fin s, DifferentialGeometry.Integral.Connection.chartTensor0SSlotCorrection (I := I) s g α
        (fun y => ContinuousMultilinearMap.domDomCongr σ
          (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I y) ℝ from T y)) X b k =
      ContinuousMultilinearMap.domDomCongr σ
        (∑ k : Fin s, DifferentialGeometry.Integral.Connection.chartTensor0SSlotCorrection (I := I) s g α
          T X b k) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]

  rw [← Equiv.sum_comp σ.symm (fun k => DifferentialGeometry.Integral.Connection.chartTensor0SSlotCorrection
    (I := I) s g α T X b k (fun i => m (σ i)))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [DifferentialGeometry.Integral.Connection.chartTensor0SSlotCorrection_apply_localSlotCLM,
    DifferentialGeometry.Integral.Connection.chartTensor0SSlotCorrection_apply_localSlotCLM]

  rw [ContinuousMultilinearMap.domDomCongr_apply]
  refine congrArg _ ?_
  funext i
  rw [localSlotCLM_comp_perm (I := I) s σ k]

private lemma domDomCongr_sub
    {n : ℕ} {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (σ : Equiv.Perm (Fin n)) (a b : ContinuousMultilinearMap ℝ (fun _ : Fin n => A) ℝ) :
    ContinuousMultilinearMap.domDomCongr σ (a - b) =
      ContinuousMultilinearMap.domDomCongr σ a - ContinuousMultilinearMap.domDomCongr σ b := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartTensor0SCovariantDerivative_succ_domDomCongr
    (s : ℕ) (g : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin (s + 1))) (α : M)
    (T : Π b : M, Tensor0SSpace (s + 1) I b) (X : Π b : M, TangentSpace I b) {b : M}
    (hb : b ∈ DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) α) :
    DifferentialGeometry.Integral.Connection.chartTensor0SCovariantDerivative (I := I) (s + 1) g α
        (fun y => ContinuousMultilinearMap.domDomCongr σ
          (show ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I y) ℝ from T y)) X b =
      ContinuousMultilinearMap.domDomCongr σ
        (DifferentialGeometry.Integral.Connection.chartTensor0SCovariantDerivative (I := I) (s + 1) g α
          T X b) := by
  classical
  have hbE : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet_mem_baseSet hb
  rw [DifferentialGeometry.Integral.Connection.chartTensor0SCovariantDerivative_succ (I := I) s g α
      (fun y => ContinuousMultilinearMap.domDomCongr σ
        (show ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I y) ℝ from T y)) X b,
    DifferentialGeometry.Integral.Connection.chartTensor0SCovariantDerivative_succ (I := I) s g α T X b]
  rw [domDomCongr_sub σ
    (DifferentialGeometry.Integral.Connection.tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b))
    (∑ k : Fin (s + 1), DifferentialGeometry.Integral.Connection.chartTensor0SSlotCorrection
      (I := I) (s + 1) g α T X b k)]
  rw [tensor0SIntrinsicChartCLM_domDomCongr (I := I) (s + 1) σ α T b hbE (X b)]
  rw [chartTensor0SSlotCorrection_sum_domDomCongr (I := I) (s + 1) g σ α T X b]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitEvalSection_tensorSectionMDiffAt
    (g : SmoothRiemannianMetric I M) (s : ℕ) (W : SmoothCcTensor g 0 s) (x : M) :
    DifferentialGeometry.Integral.Connection.TensorSectionMDiffAt (I := I) s
      (unitEvalSection (I := I) (M := M) g s W) x := by
  classical
  have hHom : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel s ℝ E))
      (fun z : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun w : M => Tensor0SSpace 0 I w →L[ℝ] Tensor0SSpace s I w) z
        (show Tensor0SSpace 0 I z →L[ℝ] Tensor0SSpace s I z from W.toSection z)) x :=
    (W.toSection.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hv : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel 0 ℝ E))
      (fun z : M => TotalSpace.mk' (Tensor0SModel 0 ℝ E)
        (E := fun w : M => Tensor0SSpace 0 I w) z (unitTensor (I := I) (M := M) z)) x :=
    (DifferentialGeometry.Integral.Connection.contMDiff_unitZeroSection
      (I := I) (M := M)).contMDiffAt.mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (b := id) hHom hv

private lemma domDomCongr_finsum_smul
    {n d : ℕ} {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (σ : Equiv.Perm (Fin n)) (c : Fin d → ℝ)
    (a : Fin d → ContinuousMultilinearMap ℝ (fun _ : Fin n => A) ℝ) :
    ContinuousMultilinearMap.domDomCongr σ (∑ i, c i • a i) =
      ∑ i, c i • ContinuousMultilinearMap.domDomCongr σ (a i) := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma tensor0SCovariantDerivative_succ_domDomCongr
    (s : ℕ) (g : SmoothRiemannianMetric I M) (σ : Equiv.Perm (Fin (s + 1)))
    (ŝ ŝ' : Π y : M, Tensor0SSpace (s + 1) I y) (x : M) (v : TangentSpace I x)
    (hŝ : DifferentialGeometry.Integral.Connection.TensorSectionMDiffAt (I := I) (s + 1) ŝ x)
    (hŝ' : DifferentialGeometry.Integral.Connection.TensorSectionMDiffAt (I := I) (s + 1) ŝ' x)
    (hrel : ∀ y : M, ŝ' y = ContinuousMultilinearMap.domDomCongr σ
      (show ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I y) ℝ from ŝ y)) :
    (show Tensor0SSpace (s + 1) I x from
        Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) ŝ' x v) =
      ContinuousMultilinearMap.domDomCongr σ
        (show Tensor0SSpace (s + 1) I x from
          Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) ŝ x v) := by
  classical
  have hx_good : x ∈ DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet (I := I) x :=
    DifferentialGeometry.Integral.Connection.self_mem_chartLeviCivitaGoodSet x
  have hxE : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    DifferentialGeometry.Integral.Connection.chartLeviCivitaGoodSet_mem_baseSet hx_good

  have hframe : ∀ i : Fin (Module.finrank ℝ E),
      (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
          (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) ŝ' x)
          (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i x) =
        ContinuousMultilinearMap.domDomCongr σ
          ((Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) ŝ x)
            (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i x)) := by
    intro i
    have hXi_at := DifferentialGeometry.Integral.Connection.chartBasisVec_alpha_mdifferentiableAt
        (I := I) x i hx_good
    rw [← DifferentialGeometry.Integral.Connection.chartTensor0SCovariantDerivative_eq_abstract_succ_aux
      (I := I) (M := M) g x s ŝ' (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i)
      hx_good hŝ' hXi_at]
    rw [show ŝ' = (fun y => ContinuousMultilinearMap.domDomCongr σ
        (show ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => TangentSpace I y) ℝ from ŝ y))
        from funext hrel]
    rw [chartTensor0SCovariantDerivative_succ_domDomCongr (I := I) s g σ x ŝ
      (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i) hx_good]
    rw [DifferentialGeometry.Integral.Connection.chartTensor0SCovariantDerivative_eq_abstract_succ_aux
      (I := I) (M := M) g x s ŝ (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i)
      hx_good hŝ hXi_at]

  conv_lhs => rw [DifferentialGeometry.Integral.Connection.chartBasisVecFiber_recompose
    (I := I) x hxE v, map_sum]
  conv_rhs => rw [DifferentialGeometry.Integral.Connection.chartBasisVecFiber_recompose
    (I := I) x hxE v, map_sum]
  simp_rw [map_smul]
  rw [domDomCongr_finsum_smul σ
    (fun i => ((DifferentialGeometry.Integral.Measure.chartModelBasis E).repr
        ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v)) i)
    (fun i => (Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
      (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) ŝ x)
      (DifferentialGeometry.Integral.Measure.chartBasisVecFiber (I := I) x i x))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hframe i]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivAt_unit_toModel_domDomCongr_of_section
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (S S' : SmoothCcTensor g 0 s)
    (hSS' : ∀ y : M, unitModel (I := I) (M := M) g s S' y =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S y))
    (x : M) (v : TangentSpace I x) :
    covDerivUnitModel (I := I) (M := M) g s S' x v =
      ContinuousMultilinearMap.domDomCongr σ
        (covDerivUnitModel (I := I) (M := M) g s S x v) := by
  classical

  rw [covDerivUnitModel_eq_tensor0SCovariantDerivative (I := I) (M := M) g s S' x v,
    covDerivUnitModel_eq_tensor0SCovariantDerivative (I := I) (M := M) g s S x v]

  have hrel : ∀ y : M, unitEvalSection (I := I) (M := M) g s S' y =
      ContinuousMultilinearMap.domDomCongr σ
        (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I y) ℝ from
          unitEvalSection (I := I) (M := M) g s S y) := by
    intro y
    have h := hSS' y
    rw [unitModel, unitModel] at h
    exact h
  rcases s with _ | s
  · have hsec : unitEvalSection (I := I) (M := M) g 0 S' = unitEvalSection (I := I) (M := M) g 0 S := by
      funext y
      have := hrel y
      rw [Subsingleton.elim σ (1 : Equiv.Perm (Fin 0))] at this
      apply ContinuousMultilinearMap.ext
      intro m
      rw [this, ContinuousMultilinearMap.domDomCongr_apply]
      exact congrArg _ (Subsingleton.elim _ _)
    rw [hsec]
    symm
    apply ContinuousMultilinearMap.ext
    intro m
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    exact congrArg _ (Subsingleton.elim _ _)
  · refine congrArg Tensor0SSpace.toModel ?_
    exact tensor0SCovariantDerivative_succ_domDomCongr (I := I) (M := M) s g σ
      (unitEvalSection (I := I) (M := M) g (s + 1) S)
      (unitEvalSection (I := I) (M := M) g (s + 1) S') x v
      (unitEvalSection_tensorSectionMDiffAt (I := I) (M := M) g (s + 1) S x)
      (unitEvalSection_tensorSectionMDiffAt (I := I) (M := M) g (s + 1) S' x)
      hrel

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma unitModel_covGrad_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) (v : Fin (s + 1) → TangentSpace I x) :
    unitModel (I := I) (M := M) g (s + 1) (covGrad (I := I) (M := M) g 0 s W) x v =
      covDerivUnitModel (I := I) (M := M) g s W x (v 0) (Matrix.vecTail v) := by
  rw [unitModel, covDerivUnitModel]
  exact covGrad_toSection_apply_eval (I := I) (M := M) g 0 s W x
    (unitTensor (I := I) (M := M) x) v

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_iteratedCovGrad_unit_toModel_domDomCongr
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (S S' : SmoothCcTensor g 0 s)
    (hSS' : ∀ y : M, unitModel (I := I) (M := M) g s S' y =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S y))
    (i : ℕ) :
    ∃ σ' : Equiv.Perm (Fin (s + i)),
      ∀ x : M, unitModel (I := I) (M := M) g (s + i)
          (show SmoothCcTensor g 0 (s + i) from
            iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S') x =
        ContinuousMultilinearMap.domDomCongr σ'
          (unitModel (I := I) (M := M) g (s + i)
            (show SmoothCcTensor g 0 (s + i) from
              iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S) x) := by
  induction i with
  | zero => exact ⟨σ, hSS'⟩
  | succ i ih =>
    obtain ⟨σ', hσ'⟩ := ih
    refine ⟨Equiv.Perm.decomposeFin.symm (0, σ'), fun x => ?_⟩
    apply ContinuousMultilinearMap.ext
    intro v

    change unitModel (I := I) (M := M) g (s + i + 1)
        (covGrad (I := I) (M := M) g 0 (s + i)
          (iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S')) x v =
      ContinuousMultilinearMap.domDomCongr (Equiv.Perm.decomposeFin.symm (0, σ'))
        (unitModel (I := I) (M := M) g (s + i + 1)
          (covGrad (I := I) (M := M) g 0 (s + i)
            (iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S)) x) v

    rw [unitModel_covGrad_apply (I := I) (M := M) g (s + i)
      (iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S') x v]
    rw [ContinuousMultilinearMap.domDomCongr_apply,
      unitModel_covGrad_apply (I := I) (M := M) g (s + i)
        (iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S) x
        (fun k => v ((Equiv.Perm.decomposeFin.symm (0, σ')) k))]

    rw [tensorCovDerivAt_unit_toModel_domDomCongr_of_section (I := I) (M := M) g (s + i) σ'
      (iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S)
      (iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S') hσ' x (v 0)]
    rw [ContinuousMultilinearMap.domDomCongr_apply]

    have hzero : v ((Equiv.Perm.decomposeFin.symm (0, σ')) (0 : Fin (s + i + 1))) = v 0 := by
      rw [Equiv.Perm.decomposeFin_symm_apply_zero]
    have htail :
        (Matrix.vecTail fun k : Fin (s + i + 1) =>
            v ((Equiv.Perm.decomposeFin.symm (0, σ')) k)) =
          fun j : Fin (s + i) => Matrix.vecTail v (σ' j) := by
      funext j
      change v ((Equiv.Perm.decomposeFin.symm (0, σ')) (Fin.succ j)) = v (Fin.succ (σ' j))
      rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
    rw [hzero, htail]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma applySection_tensorSectionMDiffAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Φ : SmoothCcTensor g r s)
    (w : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯) (x : M) :
    DifferentialGeometry.Integral.Connection.TensorSectionMDiffAt (I := I) s
      (fun y => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) (w y)) x := by
  classical
  have hHom : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E))
      (fun z : M => TotalSpace.mk' (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)
        (E := fun u : M => Tensor0SSpace r I u →L[ℝ] Tensor0SSpace s I u) z
        (show Tensor0SSpace r I z →L[ℝ] Tensor0SSpace s I z from Φ.toSection z)) x :=
    (Φ.toSection.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  have hv : MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E))
      (fun z : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun u : M => Tensor0SSpace r I u) z (w z)) x :=
    (w.contMDiff.contMDiffAt).mdifferentiableAt (by simp)
  exact MDifferentiableAt.clm_bundle_apply (b := id) hHom hv

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivAt_rs_toModel_domDomCongr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : Equiv.Perm (Fin s))
    (Φ Φ' : SmoothCcTensor g r s)
    (hrel : ∀ (y : M) (d : Tensor0SSpace r I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ'.toSection y) d) =
        ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) d)))
    (x : M) (v : TangentSpace I x) (D : Tensor0SSpace r I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          tensorCovDerivAt (I := I) (M := M) g r s Φ' x v) D) =
      ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            tensorCovDerivAt (I := I) (M := M) g r s Φ x v) D)) := by
  classical

  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel r ℝ E) (V := fun y : M => Tensor0SSpace r I y)
    (n := (⊤ : ℕ∞)) x D

  set u : Π y : M, Tensor0SSpace s I y :=
    fun y => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) (w y) with hu_def
  set u' : Π y : M, Tensor0SSpace s I y :=
    fun y => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ'.toSection y) (w y) with hu'_def
  have hu_at : DifferentialGeometry.Integral.Connection.TensorSectionMDiffAt (I := I) s u x :=
    applySection_tensorSectionMDiffAt (I := I) (M := M) g r s Φ w x
  have hu'_at : DifferentialGeometry.Integral.Connection.TensorSectionMDiffAt (I := I) s u' x :=
    applySection_tensorSectionMDiffAt (I := I) (M := M) g r s Φ' w x
  have hurel : ∀ y : M, u' y =
      ContinuousMultilinearMap.domDomCongr σ
        (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I y) ℝ from u y) := by
    intro y
    apply Tensor0SSpace.toModel_injective
    have h := hrel y (w y)
    rw [hu'_def, hu_def]
    exact h

  rw [tensorCovDerivAt_def (I := I) (M := M) g r s Φ' x v,
    tensorCovDerivAt_def (I := I) (M := M) g r s Φ x v]
  have hHL' := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) r s
    (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) Φ'.toSection w x v
  have hHL := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) r s
    (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) Φ.toSection w x v
  rw [← hw]
  rw [hHL', hHL]
  rw [Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_sub, domDomCongr_sub]

  have hsource :
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ'.toSection x)
            (Tensor0SNabla.tensor0SCovariantDerivative I M r
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) w x v)) =
        ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
              (Tensor0SNabla.tensor0SCovariantDerivative I M r
                (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) w x v))) :=
    hrel x _

  have htarget :
      Tensor0SSpace.toModel
          (Tensor0SNabla.tensor0SCovariantDerivative I M s
            (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) u' x v) =
        ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            (Tensor0SNabla.tensor0SCovariantDerivative I M s
              (DifferentialGeometry.Integral.Connection.LeviCivita (I := I) g) u x v)) := by
    rcases s with _ | s'
    · apply ContinuousMultilinearMap.ext
      intro m
      rw [ContinuousMultilinearMap.domDomCongr_apply]
      congr 1
      · have hsec : u' = u := by
          funext y
          have hy := hurel y
          rw [Subsingleton.elim σ (1 : Equiv.Perm (Fin 0))] at hy
          rw [hy]
          apply ContinuousMultilinearMap.ext
          intro m'
          rw [ContinuousMultilinearMap.domDomCongr_apply]
          exact congrArg _ (Subsingleton.elim _ _)
        rw [hsec]
      · exact Subsingleton.elim _ _
    · refine congrArg Tensor0SSpace.toModel ?_
      exact tensor0SCovariantDerivative_succ_domDomCongr (I := I) (M := M) s' g σ u u' x v
        hu_at hu'_at hurel
  rw [htarget, hsource]

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_rs_toModel_domDomCongr
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : Equiv.Perm (Fin s))
    (Φ Φ' : SmoothCcTensor g r s)
    (hrel : ∀ (y : M) (d : Tensor0SSpace r I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ'.toSection y) d) =
        ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) d)))
    (x : M) (d : Tensor0SSpace r I x) (v : Fin (s + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
          (covGrad (I := I) (M := M) g r s Φ').toSection x) d) v =
      ContinuousMultilinearMap.domDomCongr (Equiv.Perm.decomposeFin.symm (0, σ))
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            (covGrad (I := I) (M := M) g r s Φ).toSection x) d)) v := by
  classical
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g r s Φ' x d v]
  rw [ContinuousMultilinearMap.domDomCongr_apply,
    covGrad_toSection_apply_eval (I := I) (M := M) g r s Φ x d
      (fun k => v ((Equiv.Perm.decomposeFin.symm (0, σ)) k))]

  rw [tensorCovDerivAt_rs_toModel_domDomCongr (I := I) (M := M) g r s σ Φ Φ' hrel x (v 0) d]
  rw [ContinuousMultilinearMap.domDomCongr_apply]

  have hzero : v ((Equiv.Perm.decomposeFin.symm (0, σ)) (0 : Fin (s + 1))) = v 0 := by
    rw [Equiv.Perm.decomposeFin_symm_apply_zero]
  have htail :
      (Matrix.vecTail fun k : Fin (s + 1) =>
          v ((Equiv.Perm.decomposeFin.symm (0, σ)) k)) =
        fun j : Fin s => Matrix.vecTail v (σ j) := by
    funext j
    change v ((Equiv.Perm.decomposeFin.symm (0, σ)) (Fin.succ j)) = v (Fin.succ (σ j))
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
  rw [hzero, htail]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lowerAllUpperIndices_zero_apply_unitModel
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g 0 s) (x : M) (u : Fin (0 + s) → TangentSpace I x) :
    (lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W.toSection x))) u =
      (unitModel (I := I) (M := M) g s W x) (fun j => u (Fin.natAdd 0 j)) := by
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  rw [unitModel, unitTensor]
  rw [toModel_tensorRS_apply (I := I) (M := M) 0 s x (W.toSection x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)))]
  rw [Tensor0SSpace.toModel_ofModel]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma lowerAllUpperIndices_zero_domDomCongr_of_unitModel
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (S S' : SmoothCcTensor g 0 s)
    (hSS' : ∀ y : M, unitModel (I := I) (M := M) g s S' y =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S y))
    (x : M) :
    lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S'.toSection x)) =
      ContinuousMultilinearMap.domDomCongr
        ((finCongr (Nat.zero_add s)).permCongr.symm σ)
        (lowerAllUpperIndices (I := I) (M := M) g 0 s x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x))) := by
  apply ContinuousMultilinearMap.ext
  intro u
  rw [lowerAllUpperIndices_zero_apply_unitModel (I := I) (M := M) g s S' x u]
  rw [hSS' x, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [lowerAllUpperIndices_zero_apply_unitModel (I := I) (M := M) g s S x]

  congr 1
  funext j
  congr 1

  rw [Equiv.permCongr_symm, Equiv.permCongr_apply]
  apply Fin.ext
  simp

omit [NeZero (Module.finrank ℝ E)] in
theorem riemannianFiberNormSq_iteratedCovGrad_eq_of_section_domDomCongr
    (g : SmoothRiemannianMetric I M) (s : ℕ) (σ : Equiv.Perm (Fin s))
    (S S' : SmoothCcTensor g 0 s)
    (hSS' : ∀ y : M, unitModel (I := I) (M := M) g s S' y =
      ContinuousMultilinearMap.domDomCongr σ (unitModel (I := I) (M := M) g s S y))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((show SmoothCcTensor g 0 (s + i) from
          iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S').toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + i) x
        ((show SmoothCcTensor g 0 (s + i) from
          iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S).toSection x) := by
  obtain ⟨σ', hσ'⟩ :=
    exists_iteratedCovGrad_unit_toModel_domDomCongr (I := I) (M := M) g s σ S S' hSS' i
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x
      ((iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S').toSection x),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g 0 (s + i) x
      ((iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S).toSection x)]

  change covariantTensorInnerPointwise (I := I) (M := M) (0 + (s + i)) g x
        (lowerAllUpperIndices (I := I) (M := M) g 0 (s + i) x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + i) I x from
              (iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S').toSection x)))
        (lowerAllUpperIndices (I := I) (M := M) g 0 (s + i) x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + i) I x from
              (iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S').toSection x))) =
      covariantTensorInnerPointwise (I := I) (M := M) (0 + (s + i)) g x
        (lowerAllUpperIndices (I := I) (M := M) g 0 (s + i) x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + i) I x from
              (iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S).toSection x)))
        (lowerAllUpperIndices (I := I) (M := M) g 0 (s + i) x
          (TensorRSSpace.toModel
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + i) I x from
              (iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S).toSection x)))
  rw [lowerAllUpperIndices_zero_domDomCongr_of_unitModel (I := I) (M := M) g (s + i) σ'
    (iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S)
    (iteratedCovGrad (E := E) (H := H) (I := I) (M := M) g 0 s i S') hσ' x]
  rw [tensorInnerPointwise_0s_domDomCongr]

end NormedSpaceModel

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
