import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.PathIntegralFibreNormTransfer

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (pathIntegralCoeffField
  pathIntegralCoeffField_toSection pathIntegralFib pathIntegralFib_toModel)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_pathIntegralCoeffField_le_weighted_sq
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : ℝ → SmoothCcTensor g₀ r s) (S : Set ℝ) (hS : IsOpen S)
    (hSI : Set.uIcc (0:ℝ) 1 ⊆ S)
    (hjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun q : M × ℝ => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) q.1 ((Φ q.2).toSection q.1))
      ((Set.univ : Set M) ×ˢ S))
    (x : M) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Set.Icc (0 : ℝ) 1))
    (hcont : ContinuousOn (fun t : ℝ => TensorRSSpace.toModel ((Φ t).toSection x))
      (Set.Icc (0 : ℝ) 1))
    (hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((Φ t).toSection x)) ≤ w t) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x
        ((pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection x) ≤
      (∫ t in (0 : ℝ)..1, w t) ^ 2 := by
  classical
  set f : ℝ → TensorRSModel r s ℝ E :=
    fun t => TensorRSSpace.toModel ((Φ t).toSection x) with hf_def
  have hfns : riemannianFiberNormSq (I := I) (M := M) g₀ r s x
      ((pathIntegralCoeffField (I := I) (M := M) g₀ r s Φ S hS hSI hjoint).toSection x) =
      tensorPointwiseNorm (I := I) (M := M) g₀ r s x (∫ t in (0 : ℝ)..1, f t) ^ 2 := by
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise]
    rw [pathIntegralCoeffField_toSection, pathIntegralFib_toModel]
    unfold tensorPointwiseNorm
    rw [Real.sq_sqrt (tensorInnerPointwise_nonneg (I := I) (M := M) g₀ r s x _)]
  rw [hfns]
  have hbound :
      tensorPointwiseNorm (I := I) (M := M) g₀ r s x (∫ t in (0 : ℝ)..1, f t) ≤
        ∫ t in (0 : ℝ)..1, w t := by
    refine le_trans
      (tensorPointwiseNorm_intervalIntegral_le (I := I) (M := M) g₀ r s x f hcont) ?_
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t) ≤ w t := by
      intro t ht
      have hfns_t : tensorPointwiseNorm (I := I) (M := M) g₀ r s x (f t) =
          Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g₀ r s x ((Φ t).toSection x)) := by
        rw [riemannianFiberNormSq_eq_tensorInnerPointwise]; rfl
      rw [hfns_t]; exact hsup t ht
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
    · exact ((tensorPointwiseNorm_continuous (I := I) (M := M) g₀ r s x).comp_continuousOn
        hcont).intervalIntegrable_of_Icc (by norm_num)
    · exact hw_cont.intervalIntegrable_of_Icc (by norm_num)
    · exact fun t ht => hpt t ht
  have hnn : 0 ≤ tensorPointwiseNorm (I := I) (M := M) g₀ r s x (∫ t in (0 : ℝ)..1, f t) :=
    tensorPointwiseNorm_nonneg (I := I) (M := M) g₀ r s x _
  have hrhs_nn : 0 ≤ ∫ t in (0 : ℝ)..1, w t := le_trans hnn hbound
  nlinarith [hbound, hnn, hrhs_nn]

end L2
end Integral
end DifferentialGeometry

end
