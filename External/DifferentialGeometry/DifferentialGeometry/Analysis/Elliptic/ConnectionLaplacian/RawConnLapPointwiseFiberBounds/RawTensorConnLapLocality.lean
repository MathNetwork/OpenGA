import DifferentialGeometry.Geometry.Connection.Laplacian.TensorConnLaplacian

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [InnerProductSpace ℝ E] in
theorem rawTensorConnLap_eq_zero_of_eventually_zero_contMDiff [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_smooth : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y)))
    (b : M) (h_zero_nhd : ∀ᶠ x in 𝓝 b, T x = 0) :
    rawTensorConnLap (I := I) g r s T b = 0 := by
  classical
  rw [Filter.eventually_iff_exists_mem] at h_zero_nhd
  obtain ⟨V, hV_nhds, hV_eq⟩ := h_zero_nhd
  obtain ⟨U, hUV, hU_open, hbU⟩ := mem_nhds_iff.mp hV_nhds
  have hT_zero_U : ∀ y ∈ U, T y = 0 := fun y hyU => hV_eq y (hUV hyU)
  have hT_diff_b : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
      (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun w : M => TensorRSSpace r s I w) z (T z)) b :=
    (hT_smooth b).mdifferentiableAt (by simp)
  have hcov_diff_b : ∀ i : Fin (Module.finrank ℝ E),
      MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        (fun z : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun w : M => TensorRSSpace r s I w) z
          (covApply (TensorRSNabla.tensorRSCovariantDerivative I M r s
              (LeviCivita (I := I) g))
            (smoothOrthoFrame (I := I) g b i) T z)) b := by
    intro i
    set cov := TensorRSNabla.tensorRSCovariantDerivative I M r s
      (LeviCivita (I := I) g) with hcov_def
    have hT_plus : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E))
        ((∞ : WithTop ℕ∞) + 1)
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y (T y)) := by
      rw [show ((∞ : WithTop ℕ∞) + 1) = ∞ from rfl]
      exact hT_smooth
    have h_covApply :
        ContMDiffOn I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
          (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun z : M => TensorRSSpace r s I z) y
            (covApply cov (smoothOrthoFrame (I := I) g b i) T y)) Set.univ :=
      covApply_contMDiffOn (cov := cov)
        (smoothOrthoFrame_smooth (I := I) g b i) hT_plus
    have h_at : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun z : M => TensorRSSpace r s I z) y
          (covApply cov (smoothOrthoFrame (I := I) g b i) T y)) b :=
      h_covApply.contMDiffAt (Filter.univ_mem)
    exact h_at.mdifferentiableAt (by simp)
  exact rawTensorConnLap_eq_zero_of_eventually_zero (I := I) g r s
    (T := T) (U := U) hU_open hbU hT_zero_U hT_diff_b hcov_diff_b

omit [InnerProductSpace ℝ E] in
theorem rawTensorConnLap_tsupport_subset [CompleteSpace E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : Π b : M, TensorRSSpace r s I b)
    (hT_smooth : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) y (T y))) :
    tsupport (fun b : M => TensorRSSpace.toModel
        (rawTensorConnLap (I := I) g r s T b)) ⊆
      tsupport (fun b : M => TensorRSSpace.toModel (T b)) := by
  classical
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hxnot
  apply hx
  have hT_eq : (fun b : M => TensorRSSpace.toModel (T b)) =ᶠ[𝓝 x] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hxnot
  have h_zero_nhd : ∀ᶠ y in 𝓝 x, T y = 0 := by
    filter_upwards [hT_eq] with y hy
    have h_model_zero : TensorRSSpace.toModel (T y) = 0 := by
      simpa using hy
    have h_model_zero' : TensorRSSpace.toModel (T y) =
        TensorRSSpace.toModel (0 : TensorRSSpace r s I y) := by
      rw [h_model_zero, TensorRSSpace.toModel_zero]
    exact TensorRSSpace.toModel_injective h_model_zero'
  have h_zero : rawTensorConnLap (I := I) g r s T x = 0 :=
    rawTensorConnLap_eq_zero_of_eventually_zero_contMDiff (I := I) g r s
      T hT_smooth x h_zero_nhd
  change TensorRSSpace.toModel
    (rawTensorConnLap (I := I) g r s T x) = 0
  rw [h_zero, TensorRSSpace.toModel_zero]

end Connection
end Integral
end DifferentialGeometry

end
