import DifferentialGeometry.Geometry.Boundary.InducedMetric
import DifferentialGeometry.Geometry.Boundary.SurfaceMeasure
import DifferentialGeometry.Geometry.Operator.Laplacian


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

open DifferentialGeometry.Integral.Measure

def boundaryLaplacian
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : BoundaryManifold I M → ℝ}
    (hf : ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞ f) :
    BoundaryManifold I M → ℝ :=
  Δ_g (I := hI.boundaryI) (inducedMetric (I := I) (M := M) g) hf

omit [InnerProductSpace ℝ E] in
omit [FiniteDimensional ℝ E] in
@[simp] lemma boundaryLaplacian_def
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : BoundaryManifold I M → ℝ}
    (hf : ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞ f)
    (x : BoundaryManifold I M) :
    boundaryLaplacian (I := I) (M := M) g hf x =
      Δ_g (I := hI.boundaryI) (inducedMetric (I := I) (M := M) g) hf x := rfl

omit [InnerProductSpace ℝ E] in
omit [FiniteDimensional ℝ E] in
theorem boundaryLaplacian_contMDiff
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : BoundaryManifold I M → ℝ}
    (hf : ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞
      (boundaryLaplacian (I := I) (M := M) g hf) :=
  Δ_g_contMDiff (I := hI.boundaryI) (inducedMetric (I := I) (M := M) g) hf

omit [InnerProductSpace ℝ E] in
omit [FiniteDimensional ℝ E] in
theorem boundaryLaplacian_add
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f h : BoundaryManifold I M → ℝ}
    (hf : ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞ h)
    (x : BoundaryManifold I M) :
    boundaryLaplacian (I := I) (M := M) g (hf.add hh) x =
      boundaryLaplacian (I := I) (M := M) g hf x +
        boundaryLaplacian (I := I) (M := M) g hh x :=
  Δ_g_add (I := hI.boundaryI) (inducedMetric (I := I) (M := M) g) hf hh x

omit [InnerProductSpace ℝ E] in
omit [FiniteDimensional ℝ E] in
@[simp] theorem boundaryLaplacian_const
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (x : BoundaryManifold I M) :
    boundaryLaplacian (I := I) (M := M) g
      (contMDiff_const : ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞
        (fun _ : BoundaryManifold I M => c)) x = 0 :=
  Δ_g_const (I := hI.boundaryI) (inducedMetric (I := I) (M := M) g) c x

omit [InnerProductSpace ℝ E] in
omit [FiniteDimensional ℝ E] in
theorem boundaryLaplacian_eq_zero_of_boundaryless
    [I.Boundaryless] [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M)
    {f : BoundaryManifold I M → ℝ}
    (hf : ContMDiff hI.boundaryI 𝓘(ℝ, ℝ) ∞ f) :
    boundaryLaplacian (I := I) (M := M) g hf = 0 := by
  haveI : IsEmpty hI.boundaryH :=
    HasSmoothBoundary.boundaryH_isEmpty_of_boundaryless I
  haveI : IsEmpty (BoundaryManifold I M) :=
    BoundaryManifold.isEmpty_of_isEmpty_boundaryH (I := I)
  funext x
  exact (IsEmpty.false x).elim

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
