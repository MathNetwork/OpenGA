import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.FrozenFrameTrace
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.FiberNormSubadditivity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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

theorem frame_offDiag_curvature_sum_fiberNormSq_le
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    ∃ Cx : ℝ, 0 ≤ Cx ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          (∑ i : Fin (Module.finrank ℝ E),
            riemannOp (tensorCov (I := I) g 0 3) x
              (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x a x)
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)) ≤
        ((Module.finrank ℝ E : ℝ)) ^ 2 * Cx *
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x
            ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  classical
  obtain ⟨Cx, hCx_nonneg, hpair⟩ :=
    riemannOp_gradTensor_offDiag_frame_fiberNormSq_le (I := I) (M := M) g T₀ x
  refine ⟨Cx, hCx_nonneg, ?_⟩
  set rS : ℝ := riemannianFiberNormSq (I := I) (M := M) g 0 3 x
    ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) with hrS_def
  set F : Fin (Module.finrank ℝ E) → TensorRSSpace 0 3 I x := fun i =>
    riemannOp (tensorCov (I := I) g 0 3) x
      (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x a x)
      ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) with hF_def
  have hsum_le :
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x (∑ i : Fin (Module.finrank ℝ E), F i) ≤
        ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).card : ℝ) *
          ∑ i : Fin (Module.finrank ℝ E),
            riemannianFiberNormSq (I := I) (M := M) g 0 3 x (F i) :=
    riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g 0 3 x Finset.univ F
  have hper_le :
      ∑ i : Fin (Module.finrank ℝ E),
          riemannianFiberNormSq (I := I) (M := M) g 0 3 x (F i) ≤
        ∑ _i : Fin (Module.finrank ℝ E), Cx * rS :=
    Finset.sum_le_sum (fun i _ => hpair i a)
  have hcard : ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).card : ℝ) =
      (Module.finrank ℝ E : ℝ) := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hconst_sum : (∑ _i : Fin (Module.finrank ℝ E), Cx * rS) =
      (Module.finrank ℝ E : ℝ) * (Cx * rS) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 3 x (∑ i : Fin (Module.finrank ℝ E), F i)
        ≤ ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).card : ℝ) *
            ∑ i : Fin (Module.finrank ℝ E),
              riemannianFiberNormSq (I := I) (M := M) g 0 3 x (F i) := hsum_le
    _ ≤ ((Finset.univ : Finset (Fin (Module.finrank ℝ E))).card : ℝ) *
          (∑ _i : Fin (Module.finrank ℝ E), Cx * rS) := by
        refine mul_le_mul_of_nonneg_left hper_le ?_
        rw [hcard]; positivity
    _ = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) * (Cx * rS)) := by
        rw [hcard, hconst_sum]
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * Cx * rS := by ring

theorem exists_frame_offDiag_curvature_sum_fiberNormSq_bound
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    ∃ K : ℝ, 0 ≤ K ∧
      riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          (∑ i : Fin (Module.finrank ℝ E),
            riemannOp (tensorCov (I := I) g 0 3) x
              (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x a x)
              ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x)) ≤
        K * riemannianFiberNormSq (I := I) (M := M) g 0 3 x
          ((covGrad (I := I) (M := M) g 0 2 T₀).toSection x) := by
  obtain ⟨Cx, hCx_nonneg, hbound⟩ :=
    frame_offDiag_curvature_sum_fiberNormSq_le (I := I) (M := M) g T₀ x a
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * Cx, ?_, hbound⟩
  positivity

section FrozenFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem frozenFrameTrace_eq_rawTensorConnLap_fixedFrame
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b) (x y : M) :
    frozenFrameTrace (I := I) g r s T x y =
      rawTensorConnLap_fixedFrame (I := I) g r s (smoothOrthoFrame (I := I) g x) T y := by
  rw [frozenFrameTrace_def, rawTensorConnLap_fixedFrame_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tensorSecondCovDeriv_def]

omit [CompactSpace M] [I.Boundaryless] in
theorem frozenFrameTrace_eq_rawTensorConnLap_of_mem_nbhd
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x) :
    frozenFrameTrace (I := I) g r s T x y = rawTensorConnLap (I := I) g r s T y := by
  rw [frozenFrameTrace_eq_rawTensorConnLap_fixedFrame]
  exact (rawTensorConnLap_eq_fixedFrame_of_orthonormal (I := I) g r s T hT_total
    (B := smoothOrthoFrame (I := I) g x)
    (fun i => smoothOrthoFrame_smooth (I := I) g x i) y
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g x hy i j)).symm

omit [CompactSpace M] [I.Boundaryless] in
theorem rawTensorConnLap_eventuallyEq_frozenFrameTrace
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_total : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (x : M) :
    ∀ᶠ y in 𝓝 x, rawTensorConnLap (I := I) g r s T y =
      frozenFrameTrace (I := I) g r s T x y := by
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x] with y hy
  exact (frozenFrameTrace_eq_rawTensorConnLap_of_mem_nbhd (I := I) g r s T hT_total x hy).symm

end FrozenFrame

end Connection
end Integral
end DifferentialGeometry

end
