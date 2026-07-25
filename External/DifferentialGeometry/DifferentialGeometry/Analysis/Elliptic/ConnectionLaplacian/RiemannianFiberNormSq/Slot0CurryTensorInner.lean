import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Slot0CurryReconstruction
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge

noncomputable section

set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators RealInnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem tensorInnerPointwise_succ_eq_sum_slot0Curry
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A B : TensorRSSpace 0 (s + 1) I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      tensorInnerPointwise (I := I) (M := M) g 0 (s + 1) x
          (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
            (r := 0) (s := s + 1) (x := x) A)
          (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
            (r := 0) (s := s + 1) (x := x) B) =
        ∑ a : Fin n,
          tensorInnerPointwise (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
              (r := 0) (s := s) (x := x)
              (slot0Curry (I := I) (M := M) g x s e K₀ A a))
            (TensorRSSpace.toModel (𝕜 := ℝ) (E := E) (I := I) (M := M)
              (r := 0) (s := s) (x := x)
              (slot0Curry (I := I) (M := M) g x s e K₀ B a)) := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hparseval, _hexp, _hrepr⟩ :=
    tangent_orthonormalBasisS_witness (I := I) (M := M) g s x
  have hn' : n = Module.finrank ℝ E := hn
  refine ⟨n, e, fun k => k.elim0, hn, ?_⟩
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g 0 (s + 1) x e bse hn' hbse
    horth A B]
  rw [Finset.sum_eq_single K₀]
  · rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin n))
          (fun (pr : Fin n × (Fin s → Fin n)) =>
            fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) A n e K₀
                (Fin.cons pr.1 pr.2) *
              fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) B n e K₀
                (Fin.cons pr.1 pr.2))
          (fun J : Fin (s + 1) → Fin n =>
            fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) A n e K₀ J *
              fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) B n e K₀ J)
          (fun pr => by simp [Fin.consEquiv])]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [tensorInnerPointwise_eq_sum_componentS_mul (I := I) (M := M) g 0 s x e bse hn' hbse
      horth (slot0Curry (I := I) (M := M) g x s e K₀ A a)
      (slot0Curry (I := I) (M := M) g x s e K₀ B a)]
    rw [Finset.sum_eq_single K₀]
    · refine Finset.sum_congr rfl (fun J' _ => ?_)
      rw [fiberNormSqComponent_slot0Curry (I := I) (M := M) g x s e K₀ A a J',
        fiberNormSqComponent_slot0Curry (I := I) (M := M) g x s e K₀ B a J']
    · intro K _ hK
      exact absurd (Subsingleton.elim K K₀) hK
    · intro h; exact absurd (Finset.mem_univ K₀) h
  · intro K _ hK
    exact absurd (Subsingleton.elim K K₀) hK
  · intro h; exact absurd (Finset.mem_univ K₀) h

end Connection
end Integral
end DifferentialGeometry

end
