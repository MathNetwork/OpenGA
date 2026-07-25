import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LieDerivativePairing
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter Tensor0SBundle ContinuousLinearMap
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

def bilinFormToModel (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (F →L[ℝ] F →L[ℝ] ℝ) ≃ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => F) ℝ :=
  ((ContinuousLinearEquiv.refl ℝ F).arrowCongr
      (continuousMultilinearCurryFin1 ℝ F ℝ).symm.toContinuousLinearEquiv).toLinearEquiv.trans
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => F) ℝ).symm.toLinearEquiv

theorem bilinFormToModel_apply (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] F →L[ℝ] ℝ) (v : Fin 2 → F) :
    bilinFormToModel F B v = B (v 0) (v 1) := by
  classical
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => F) ℝ).symm
      (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
          (continuousMultilinearCurryFin1 ℝ F ℝ).symm.toContinuousLinearEquiv) B) v =
    B (v 0) (v 1)
  rw [continuousMultilinearCurryLeftEquiv_symm_apply,
    ContinuousLinearEquiv.arrowCongr_apply]
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [continuousMultilinearCurryFin1_symm_apply]
  rfl

theorem bilinFormToModel_symm_apply (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => F) ℝ) (v w : F) :
    (bilinFormToModel F).symm T v w = T ![v, w] := by
  classical
  have h := bilinFormToModel_apply F ((bilinFormToModel F).symm T) ![v, w]
  rw [(bilinFormToModel F).apply_symm_apply T] at h
  simpa using h.symm

theorem bilinFormToModel_norm_map (F : Type*)
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] F →L[ℝ] ℝ) :
    ‖bilinFormToModel F B‖ = ‖B‖ := by
  classical
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg B) (fun m => ?_)
    rw [bilinFormToModel_apply]
    rw [Fin.prod_univ_two]
    calc ‖B (m 0) (m 1)‖
        ≤ ‖B‖ * ‖m 0‖ * ‖m 1‖ := B.le_opNorm₂ (m 0) (m 1)
      _ = ‖B‖ * (‖m 0‖ * ‖m 1‖) := by ring
  · refine ContinuousLinearMap.opNorm_le_bound₂ B (norm_nonneg _) (fun v w => ?_)
    have hsymm : B v w = bilinFormToModel F B ![v, w] := by
      conv_lhs => rw [← (bilinFormToModel F).symm_apply_apply B]
      rw [bilinFormToModel_symm_apply]
    rw [hsymm]
    calc ‖bilinFormToModel F B ![v, w]‖
        ≤ ‖bilinFormToModel F B‖ * ∏ i : Fin 2, ‖(![v, w] : Fin 2 → F) i‖ :=
          (bilinFormToModel F B).le_opNorm _
      _ = ‖bilinFormToModel F B‖ * ‖v‖ * ‖w‖ := by
          rw [Fin.prod_univ_two]; simp [Matrix.cons_val_zero, Matrix.cons_val_one]; ring

def bilinFormToModelₗᵢ (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (F →L[ℝ] F →L[ℝ] ℝ) ≃ₗᵢ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 2 => F) ℝ :=
  { bilinFormToModel F with norm_map' := bilinFormToModel_norm_map F }

private def deTurckRHSModelFun (g_bg g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x :=
  Tensor0SSpace.ofModel
    (bilinFormToModel (TangentSpace I x) (deTurckRicciRHS (I := I) g_bg g x))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem deTurckRHSModelFun_toModel_apply
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (deTurckRHSModelFun (I := I) g_bg g x) v =
      deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) := by
  unfold deTurckRHSModelFun
  rw [Tensor0SSpace.toModel_ofModel]
  exact bilinFormToModel_apply (TangentSpace I x) (deTurckRicciRHS (I := I) g_bg g x) v

def deTurckRHSField (g_bg g : SmoothRiemannianMetric I M) :
    Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  letI := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := ∞)
  ⟨fun x => deTurckRHSModelFun (I := I) g_bg g x, by
    let d := Module.finrank ℝ E
    let b : Module.Basis (Fin d) ℝ E := chartModelBasis E
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
      fun σ x₀ => ?_
    have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x : M =>
          deTurckRicciRHS (I := I) g_bg g x
            (chartFrameVec (I := I) x₀ (σ 0) x)
            (chartFrameVec (I := I) x₀ (σ 1) x))
        (chartAt H x₀).source :=
      combine_smoothness_of_summands (I := I) g_bg g x₀ (σ 0) (σ 1)
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
    change Tensor0SSpace.toModel (deTurckRHSModelFun (I := I) g_bg g x)
        (fun j => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ j))) = _
    rw [deTurckRHSModelFun_toModel_apply]
    rfl⟩

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckRHSField_toModel_apply
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel (deTurckRHSField (I := I) g_bg g x) v =
      deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) :=
  deTurckRHSModelFun_toModel_apply (I := I) g_bg g x v

def deTurckRHSMixedSection (g_bg g : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun x : M => TensorRSSpace 0 2 I x)⟯ :=
  MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ (deTurckRHSField (I := I) g_bg g)

def deTurckRHSSection (g_bg g : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 0 2 where
  toSection := deTurckRHSMixedSection (I := I) g_bg g
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp] theorem deTurckRHSSection_toSection
    (g_bg g : SmoothRiemannianMetric I M) :
    (deTurckRHSSection (I := I) g_bg g).toSection =
      deTurckRHSMixedSection (I := I) g_bg g := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckRHSSection_toModel_apply
    (g_bg g : SmoothRiemannianMetric I M) (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((deTurckRHSSection (I := I) g_bg g).toSection x
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v =
      deTurckRicciRHS (I := I) g_bg g x (v 0) (v 1) := by
  classical
  rw [deTurckRHSSection_toSection]
  change Tensor0SSpace.toModel
      ((MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (deTurckRHSField (I := I) g_bg g x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) v = _
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul,
    deTurckRHSField_toModel_apply]

end RicciFlow
end PDE
end DifferentialGeometry

end
