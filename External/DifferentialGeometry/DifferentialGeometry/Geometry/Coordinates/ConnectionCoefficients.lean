import DifferentialGeometry.Geometry.Coordinates.Christoffel
import DifferentialGeometry.Geometry.Coordinates.CoordinateFrame
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder

set_option autoImplicit false
set_option linter.style.longLine false









noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open Bundle Set TensorLieDeriv Filter
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]



omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
theorem tangentConstInChart_eq_coordinateFrame_eventually
    (x₀ : M) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ ((Module.finBasis 𝕜 E) i) :
        (x : M) → TangentSpace I x) =ᶠ[𝓝 x₀]
      coordinateFrameAt (I := I) x₀ i := by
  filter_upwards
    [((coordinateTrivializationAt (I := I) x₀).open_baseSet.mem_nhds
      (coordinateFrameAt_mem (I := I) x₀))] with x hx
  have hx_src : x ∈ (chartAt H x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  rw [tangentConstInChart_apply]
  rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hx_src]
  rw [coordinateFrameAt_apply_of_mem (I := I) (x₀ := x₀) (x := x) hx i]
  rfl

set_option linter.flexible false in


theorem connCoeff_eq_christoffelAlong_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : (x : M) -> TangentSpace I x) (x₀ : M)
    (j k : CoordinateIdx (𝕜 := 𝕜) E) :
    connectionEndomorphismCoeff (𝕜 := 𝕜) (E := E) (Module.finBasis 𝕜 E)
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov X x₀
          (extChartAt I x₀ x₀)) j k =
      christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        x₀ (X x₀) j k := by
  classical
  let e := coordinateTrivializationAt (I := I) x₀
  have hx_base : x₀ ∈ e.baseSet := by
    simp [e, coordinateTrivializationAt]
  have hconst :
      MDiffAt
        (T% (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
          ((Module.finBasis 𝕜 E) j) : (x : M) → TangentSpace I x)) x₀ :=
    mdifferentiableAt_tangentConstInChart_of_mem
      (𝕜 := 𝕜) (I := I) (x₀ := x₀) (p := x₀)
      ((Module.finBasis 𝕜 E) j) hx_base
  have hframe :
      MDiffAt (T% (coordinateFrameAt (I := I) x₀ j)) x₀ :=
    ((coordinateFrameAt_isLocalFrame_one (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) j).mdifferentiableAt one_ne_zero
  have hcov :
      cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
            ((Module.finBasis 𝕜 E) j)) x₀ =
        cov (coordinateFrameAt (I := I) x₀ j) x₀ :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hconst hframe
      (by simp)
      (tangentConstInChart_eq_coordinateFrame_eventually (I := I) x₀ j)
  unfold connectionEndomorphismCoeff christoffelAlongInFrame
  rw [connectionEndomorphismInChart_apply_of_mem
    (𝕜 := 𝕜) (I := I) cov X x₀ (mem_extChartAt_target x₀)
    ((Module.finBasis 𝕜 E) j)]
  rw [extChartAt_to_inv]
  rw [hcov]
  rw [coordinateFrameAt_coeff_eq_toBasis_coord]
  rw [coordinateFrameAt_toBasis_eq_finBasis]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt
    (I := I) (x₀ := x₀) (x := x₀) (mem_chart_source H x₀)]
  rw [mfderiv_extChartAt_self]
  rfl

end DifferentialGeometry.Tensor.Coordinates
