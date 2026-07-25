import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Torsion































namespace DifferentialGeometry
namespace Integral
namespace Connection

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]







omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem leviCivitaConnectionOfMetric_apply_eq_leviCivita
    (g : Measure.SmoothRiemannianMetric I M)
    {σ : Π x : M, TangentSpace I x} {x : M} (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    (leviCivitaConnectionOfMetric (I := I) g).toFun σ x v
      = (LeviCivita (I := I) g).toFun σ x v := by
  refine LeviCivita_unique g (leviCivitaConnectionOfMetric (I := I) g) ?_ ?_ hσ v
  · funext y
    exact (leviCivitaConnectionOfMetric_isLeviCivita (I := I) g).2 y
  ·


    intro Y Z x hY hZ _ w
    classical
    obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
      (F := E) (V := (TangentSpace I : M → Type _)) x w
    have hX : MDiffAt (T% fun y => X y) x := X.mdifferentiableAt
    have h := metric_compatible_at_apply
      ((leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) x) X Y Z hX hY hZ
    rw [hXx] at h
    exact h

end Connection
end Integral
end DifferentialGeometry
