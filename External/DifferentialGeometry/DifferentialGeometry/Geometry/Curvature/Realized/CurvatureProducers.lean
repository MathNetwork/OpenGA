import DifferentialGeometry.Geometry.Curvature.Realized.CurvatureTensor
import DifferentialGeometry.Geometry.Connection.LeviCivita.Basic
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Pointwise
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections

set_option autoImplicit false
set_option linter.style.longLine false












noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]




structure CurvatureSectionProducerData
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) where
  rm13 : Tensor13Section (I := I) (M := M)
  rm04 : Tensor04Section (I := I) (M := M)
  ricci : Tensor02Section (I := I) (M := M)
  h_rm13 : Rm13RealizesConnection (I := I) cov rm13
  h_rm04 : Rm04RealizesConnection (I := I) g cov rm04
  h_ricci13 : RicciTensorRealizesRm13Trace (I := I) ricci rm13

namespace CurvatureSectionProducerData

omit [T2Space M] in
theorem rm13_from_connection
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (K : CurvatureSectionProducerData (I := I) cov g) :
    Rm13RealizesConnection (I := I) cov K.rm13 :=
  K.h_rm13

omit [T2Space M] in
theorem rm04_from_rm13
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (K : CurvatureSectionProducerData (I := I) cov g) :
    Rm04RealizesConnection (I := I) g cov K.rm04 :=
  K.h_rm04

omit [T2Space M] in
theorem ricci_from_rm13
    {cov : CovariantDerivative I E (TangentSpace I : M -> Type _)}
    {g : SmoothRiemannianMetric I M}
    (K : CurvatureSectionProducerData (I := I) cov g) :
    RicciTensorRealizesRm13Trace (I := I) K.ricci K.rm13 :=
  K.h_ricci13

end CurvatureSectionProducerData












theorem rm13Section_realizes
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) :
    Rm13RealizesConnection (I := I) cov
      (DifferentialGeometry.Integral.Connection.CovariantDerivative.rm13Section (I := I) (M := M) cov hcov) := by
  intro X Y Z x alpha
  exact
    DifferentialGeometry.Integral.Connection.CovariantDerivative.rm13Section_apply_smooth
      (I := I) (M := M) cov hcov X Y Z alpha



theorem rm04Section_realizes
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞) :
    Rm04RealizesConnection (I := I) g cov
      (DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section (I := I) g cov hcov) := by
  intro X Y Z W x
  exact
    DifferentialGeometry.Integral.Connection.CovariantDerivative.rm04Section_apply_smooth
      (I := I) (M := M) g cov hcov X Y Z W x

end DifferentialGeometry.Integral.Connection
