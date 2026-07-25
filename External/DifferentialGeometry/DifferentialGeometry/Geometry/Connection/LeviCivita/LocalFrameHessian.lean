import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.LeviCivita
import DifferentialGeometry.Geometry.Connection.LeviCivita.Curvature.Realized

set_option autoImplicit false
set_option linter.style.longLine false















noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped BigOperators Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]






def scalHessFrame
    (g : SmoothRiemannianMetric I M)
    {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain)
    (gInv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  let cov := leviCivitaConnectionOfMetric (I := I) g
  let hcov :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := I) (M := M) g
  let Ric : Tensor02Section (I := I) (M := M) :=
    DifferentialGeometry.Integral.Connection.CovariantDerivative.ricciSection (I := I) (M := M) cov hcov
  let nablaRic :=
    totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      2 cov Ric (totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
        2 cov hcov Ric)
  let nabla2Ric :=
    totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      3 cov nablaRic x
  ∑ k : CoordinateIdx (𝕜 := Real) E,
    ∑ l : CoordinateIdx (𝕜 := Real) E,
      gInv k l *
        nabla2Ric (vec4 (I := I) (F.basisAt hx i) (F.basisAt hx j)
          (F.basisAt hx k) (F.basisAt hx l))







omit [FiniteDimensional ℝ E] in
theorem scalHessFrameSymm
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M)
    {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain)
    (gInv :
      CoordinateIdx (𝕜 := Real) E -> CoordinateIdx (𝕜 := Real) E -> Real)
    (hinv :
      MetricInverseInBasis_gen (I := I) (M := M) g x (F.basisAt hx) gInv)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    scalHessFrame (I := I) (M := M) g F hx gInv i j =
      scalHessFrame (I := I) (M := M) g F hx gInv j i := by
  simpa [scalHessFrame] using
    DifferentialGeometry.Integral.Connection.canScalHess (I := I) (M := M) (g := g)
      (basis := F.basisAt hx) gInv hinv i j






def frameInvMetric
    (g : SmoothRiemannianMetric I M)
    {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  basisInvMetric (I := I) (M := M) g x (F.basisAt hx) i j



omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [IsManifold I 1 M] [SigmaCompactSpace M] [T2Space M] in
theorem frameInvMetric_real
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M)
    {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain) :
    MetricInverseInBasis_gen (I := I) (M := M) g x (F.basisAt hx)
      (frameInvMetric (I := I) (M := M) g F hx) := by
  simpa [frameInvMetric] using
    basisInvMetric_real (I := I) (M := M) (g := g) (x := x)
      (basis := F.basisAt hx)


def frameScalHess
    (g : SmoothRiemannianMetric I M)
    {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain)
    (i j : CoordinateIdx (𝕜 := Real) E) : Real :=
  scalHessFrame (I := I) (M := M) g F hx
    (frameInvMetric (I := I) (M := M) g F hx) i j



omit [FiniteDimensional ℝ E] in
theorem frameScalHess_symm
    [FiniteDimensional Real E]
    (g : SmoothRiemannianMetric I M)
    {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    frameScalHess (I := I) (M := M) g F hx i j =
      frameScalHess (I := I) (M := M) g F hx j i := by
  simpa [frameScalHess] using
    scalHessFrameSymm (I := I) (M := M) g F hx
      (frameInvMetric (I := I) (M := M) g F hx)
      (frameInvMetric_real (I := I) (M := M) g F hx) i j

end DifferentialGeometry.Integral.Connection
