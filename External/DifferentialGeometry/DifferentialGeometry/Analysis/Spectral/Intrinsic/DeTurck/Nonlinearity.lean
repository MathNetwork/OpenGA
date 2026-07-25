import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Linearization
import DifferentialGeometry.Analysis.Sobolev.Embedding.TensorSobolevEmbeddingCm
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.HilbertSpace
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHS
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Integrability
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartFiberTrivialisationOpNorm.SmoothBilinearSectionBddAbove













noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open Bundle ContinuousLinearMap Tensor0SBundle
open scoped Manifold ContDiff
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]























private def retag (g₀ : SmoothRiemannianMetric I M)
    {g : SmoothRiemannianMetric I M} (S : SmoothCcTensor g 0 2) :
    SmoothCcTensor g₀ 0 2 where
  toSection := S.toSection
  hasCompactSupport := S.hasCompactSupport

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] private theorem retag_toFun (g₀ : SmoothRiemannianMetric I M)
    {g : SmoothRiemannianMetric I M} (S : SmoothCcTensor g 0 2) :
    (retag (I := I) g₀ S).toFun = S.toFun := rfl



private def rhsDiffSection (g_bg g g' g₀ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 2 :=
  retag (I := I) g₀ (deTurckRHSSection (I := I) g_bg g) -
    retag (I := I) g₀ (deTurckRHSSection (I := I) g_bg g')



private def rhsDiffGNorm (g_bg g g' g₀ : SmoothRiemannianMetric I M) (y : M) : ℝ :=
  tensorPointwiseNorm (I := I) (M := M) g₀ 0 2 y
    ((rhsDiffSection (I := I) g_bg g g' g₀).toFun y)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem rhsDiffGNorm_nonneg
    (g_bg g g' g₀ : SmoothRiemannianMetric I M) (y : M) :
    0 ≤ rhsDiffGNorm (I := I) g_bg g g' g₀ y :=
  Real.sqrt_nonneg _




omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem continuous_rhsDiffGNorm_sq
    (g_bg g g' g₀ : SmoothRiemannianMetric I M) :
    Continuous (fun y : M =>
      tensorInnerPointwise (I := I) (M := M) g₀ 0 2 y
        ((rhsDiffSection (I := I) g_bg g g' g₀).toFun y)
        ((rhsDiffSection (I := I) g_bg g g' g₀).toFun y)) :=
  SmoothCcTensor.continuous_inner_self (I := I) (M := M)
    (rhsDiffSection (I := I) g_bg g g' g₀)



omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem continuous_rhsDiffGNorm
    (g_bg g g' g₀ : SmoothRiemannianMetric I M) :
    Continuous (rhsDiffGNorm (I := I) g_bg g g' g₀) :=
  Real.continuous_sqrt.comp (continuous_rhsDiffGNorm_sq (I := I) g_bg g g' g₀)

















omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem bddAbove_gNorm_range (g_bg g g' g₀ : SmoothRiemannianMetric I M) :
    BddAbove (Set.range (rhsDiffGNorm (I := I) g_bg g g' g₀)) :=
  (isCompact_range (continuous_rhsDiffGNorm (I := I) g_bg g g' g₀)).bddAbove

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem rhsDiffSection_toModel_apply
    (g_bg g g' g₀ : SmoothRiemannianMetric I M) (y : M)
    (v : Fin 2 → TangentSpace I y) :
    Tensor0SSpace.toModel
        ((rhsDiffSection (I := I) g_bg g g' g₀).toSection y
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I y) (1 : ℝ))) v =
      deTurckRicciRHS (I := I) g_bg g y (v 0) (v 1) -
        deTurckRicciRHS (I := I) g_bg g' y (v 0) (v 1) := by
  have h_sec :
      (rhsDiffSection (I := I) g_bg g g' g₀).toSection y =
        (deTurckRHSSection (I := I) g_bg g).toSection y -
          (deTurckRHSSection (I := I) g_bg g').toSection y := rfl
  rw [h_sec]
  rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.sub_apply]
  rw [deTurckRHSSection_toModel_apply (I := I) g_bg g y v,
    deTurckRHSSection_toModel_apply (I := I) g_bg g' y v]


























omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem deturck_ricci_rhs_nonlinearity_locally_lipschitz
    (g_bg g₀ : SmoothRiemannianMetric I M) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (g g' : SmoothRiemannianMetric I M) (y : M),
        tensorPointwiseNorm (I := I) (M := M) g₀ 0 2 y
            ((rhsDiffSection (I := I) g_bg g g' g₀).toFun y) ≤
          L *
            (⨆ z : M, tensorPointwiseNorm (I := I) (M := M) g₀ 0 2 z
              ((rhsDiffSection (I := I) g_bg g g' g₀).toFun z)) := by
  refine ⟨1, by norm_num, ?_⟩
  intro g g' y
  rw [one_mul]
  change rhsDiffGNorm (I := I) g_bg g g' g₀ y ≤
    ⨆ z : M, rhsDiffGNorm (I := I) g_bg g g' g₀ z
  exact le_ciSup (bddAbove_gNorm_range (I := I) g_bg g g' g₀) y

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
