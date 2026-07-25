import DifferentialGeometry.Geometry.Metric.SmoothVectorFieldExt
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.BumpFunction





















noncomputable section


open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]


theorem exists_contMDiff_vectorField_eq (q : M) (v : TangentSpace I q) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x (V x)) ∧
      V q = v := by
  classical
  set c : E := (trivializationAt E (TangentSpace I) q ⟨q, v⟩).2 with hc
  let f : SmoothBumpFunction I q := Classical.arbitrary _
  have htsupp : tsupport (⇑f) ⊆ (trivializationAt E (TangentSpace I) q).baseSet := by
    have h1 := f.tsupport_subset_extChartAt_source
    rw [extChartAt_source] at h1
    exact h1
  refine ⟨fun x => f x • chartConstVecFiber (I := I) q c x, ?_, ?_⟩
  · exact ContMDiffOn.smul_section_of_tsupport
      (f.contMDiff.contMDiffOn) (trivializationAt E (TangentSpace I) q).open_baseSet htsupp
      (chartConstVec_contMDiffOn (I := I) q c)
  · have hf1 : f q = 1 := f.eventuallyEq_one.self_of_nhds
    change f q • chartConstVecFiber (I := I) q c q = v
    rw [hf1, one_smul, chartConstVecFiber_self]

end Riemannian
end Geometry
end DifferentialGeometry

end
