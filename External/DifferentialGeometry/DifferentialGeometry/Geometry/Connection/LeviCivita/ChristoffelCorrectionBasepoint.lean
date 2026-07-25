import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartTorsion


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma trivToE_basepoint (α : M) (v : TangentSpace I α) :
    trivToE (I := I) α α v = v := by
  classical
  have hcore : trivToE (I := I) α α
      = (tangentBundleCore I M).coordChange (achart H α) (achart H α) α :=
    TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) (M := M)
      (b₀ := α) (b := α) (mem_chart_source H α)
  rw [hcore]
  exact (tangentBundleCore I M).coordChange_self (achart H α) α
    (by rw [tangentBundleCore_baseSet]; exact mem_chart_source H α) v

omit [NeZero (Module.finrank ℝ E)] in
theorem christoffelCorrection_basepoint_apply
    (g : SmoothRiemannianMetric I M) (α : M) (Y : E) (w : TangentSpace I α) :
    christoffelCorrection (I := I) g α α Y w =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (((chartModelBasis E).repr w) i *
                ((chartModelBasis E).repr Y) j *
                chartChristoffel (I := I) g α i j k (extChartAt I α α)) •
              (chartModelBasis E) k := by
  classical
  rw [christoffelCorrection_apply]
  rw [trivToE_basepoint (I := I) α w]

omit [NeZero (Module.finrank ℝ E)] in
theorem christoffelCorrection_basepoint_symm
    (g : SmoothRiemannianMetric I M) (α : M) (Y w : TangentSpace I α) :
    christoffelCorrection (I := I) g α α Y w =
      christoffelCorrection (I := I) g α α w Y := by
  classical
  have hsym := christoffelCorrection_symm_cancel (I := I) g α α w Y
  rw [trivToE_basepoint (I := I) α Y, trivToE_basepoint (I := I) α w] at hsym
  exact hsym

end Connection
end Integral
end DifferentialGeometry
