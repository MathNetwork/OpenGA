import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Curvature.Components.RicciTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Trace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRaisingBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBoundsFlow

set_option autoImplicit false










noncomputable section

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Integral.Connection Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M]




omit [I.Boundaryless] in
theorem ricciAt_unitQuad_le_of_sol
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    {t : Real} (ht : t ∈ D.carrier) (x : M) (u : TangentSpace I x)
    (hu : (S.base.metric t).inner x u u = 1) :
    |S.ricciAt t x (vec2 (I := I) u u)|
      ≤ (Module.finrank Real (TangentSpace I x) : Real) ^ 2
          * Real.sqrt (normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x)) := by
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) (S.base.metric t) x
  have hinv : MetricInverseInBasis_gen (I := I) (S.base.metric t) x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) (S.base.metric t) basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  have hbridge : ∀ i j : Fin (Module.finrank Real (TangentSpace I x)),
      (S.ricci t) x (vec2 (I := I) (basis i) (basis j))
        = S.ricciAt t x (vec2 (I := I) (basis i) (basis j)) := by
    intro i j; simp
  have htrace : ∀ i j : Fin (Module.finrank Real (TangentSpace I x)),
      S.ricciAt t x (vec2 (I := I) (basis i) (basis j))
        = ∑ a, S.base.rm04 t x
            (vec4 (I := I) (basis a) (basis i) (basis j) (basis a)) := by
    intro i j
    have h :=
      ricci_diag_eq_sum_rm04_diag_of_orthonormal (I := I) (S.base.metric t) basis
        (S.ricci t) (S.base.rm13 t) (S.base.rm04 t)
        (DifferentialGeometry.PDE.RicciFlow.ricciTraceOfSol (I := I) S t ht)
        (DifferentialGeometry.PDE.RicciFlow.solution_rm04LowersRm13At (I := I) S t x) hON i j
    rw [hbridge i j] at h
    exact h
  exact ricci_unitQuad_le_of_trace (I := I) (S.base.metric t) basis hON hinv
    (S.ricciAt t x) (S.base.rm04 t x) htrace u hu





omit [I.Boundaryless] in
theorem twoTensorQuadBound_of_solutions
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (S : Nat -> DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := M) D)
    (K : Set M) (β ψ C : Real) (hC : 0 <= C)
    (hwin : Set.Icc β ψ ⊆ D.carrier)
    (hcurv : forall i : Nat, forall t : Real, t ∈ Set.Icc β ψ -> forall x : M, x ∈ K ->
      normSq0S (I := I) ((S i).base.metric t) x 4 ((S i).base.rm04 t x) <= C) :
    DifferentialGeometry.HCGCompactness.TwoTensorQuadBoundOnWindow (I := I) K β ψ
      (fun i s => (S i).base.metric s) (fun i t x => (S i).ricciAt t x)
      ((Module.finrank Real E : Real) ^ 2 * Real.sqrt C) := by
  refine DifferentialGeometry.HCGCompactness.twoTensorQuadBound_of_unit_bound K β ψ
    ((Module.finrank Real E : Real) ^ 2 * Real.sqrt C)
    (fun i s => (S i).base.metric s) (fun i t x => (S i).ricciAt t x)
    (by positivity) ?_
  intro i t ht x hx u hu
  calc |(S i).ricciAt t x (vec2 (I := I) u u)|
      ≤ (Module.finrank Real (TangentSpace I x) : Real) ^ 2
          * Real.sqrt (normSq0S (I := I) ((S i).base.metric t) x 4 ((S i).base.rm04 t x)) :=
        ricciAt_unitQuad_le_of_sol (S i) (hwin ht) x u hu
    _ ≤ (Module.finrank Real E : Real) ^ 2 * Real.sqrt C := by
        have hfr : Module.finrank Real (TangentSpace I x) = Module.finrank Real E := rfl
        rw [hfr]
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (hcurv i t ht x hx)) (by positivity)

end DifferentialGeometry.Integral.Connection
