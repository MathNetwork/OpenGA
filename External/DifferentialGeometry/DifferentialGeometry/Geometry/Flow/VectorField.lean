import DifferentialGeometry.Geometry.Flow.VectorFieldSmooth

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace PDE
namespace DeTurck

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def deTurckVF (g g' : SmoothRiemannianMetric I M) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨fun x : M => deTurckFun (I := I) g g' x, deTurckFun_contMDiff_total (I := I) g g'⟩

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
@[simp]
theorem deTurckVF_apply (g g' : SmoothRiemannianMetric I M) (x : M) :
    (deTurckVF (I := I) g g' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      deTurckFun (I := I) g g' x := rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckVF_self (g : SmoothRiemannianMetric I M) :
    deTurckVF (I := I) g g = 0 := by
  ext x
  rw [deTurckVF_apply, deTurckFun_self_apply (I := I) g x]
  rw [ContMDiffSection.coe_zero]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem deTurckVF_apply_eq (g g' : SmoothRiemannianMetric I M) (x : M) :
    (deTurckVF (I := I) g g' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x j k •
          connDiff (I := I) g g' x
            (chartBasisVecFiber (I := I) x j x)
            (chartBasisVecFiber (I := I) x k x) := by
  rw [deTurckVF_apply, deTurckFun_def, deTurckChartLocal_def]

end DeTurck
end PDE
end DifferentialGeometry
