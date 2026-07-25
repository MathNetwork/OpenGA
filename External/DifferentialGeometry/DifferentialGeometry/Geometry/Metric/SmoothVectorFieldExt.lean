import DifferentialGeometry.Geometry.Metric.ChartGram



















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


def chartConstVecFiber (x₀ : M) (c : E) (x : M) : TangentSpace I x :=
  (trivializationAt E (TangentSpace I) x₀).symm x c


omit [FiniteDimensional ℝ E] in
lemma chartConstVecFiber_self (q : M) (v : TangentSpace I q) :
    chartConstVecFiber (I := I) q
      ((trivializationAt E (TangentSpace I) q ⟨q, v⟩).2) q = v := by
  have hq : q ∈ (trivializationAt E (TangentSpace I) q).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) q
  simp only [chartConstVecFiber]
  exact (trivializationAt E (TangentSpace I) q).symm_apply_apply_mk hq v


omit [FiniteDimensional ℝ E] in
lemma chartConstVec_contMDiffOn (x₀ : M) (c : E) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E (E := fun y : M => TangentSpace I y) x
        (chartConstVecFiber (I := I) x₀ c x))
      (trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hiff :=
    ((trivializationAt E (TangentSpace I) x₀)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞) (s := fun x => chartConstVecFiber (I := I) x₀ c x)
  refine hiff.mpr ?_
  refine (contMDiffOn_const (c := c)).congr ?_
  intro x hx
  have h := (trivializationAt E (TangentSpace I) x₀).apply_mk_symm hx c
  simpa [chartConstVecFiber] using congrArg Prod.snd h

end Riemannian
end Geometry
end DifferentialGeometry

end
