import DifferentialGeometry.Geometry.Curvature.PullbackNaturality
import DifferentialGeometry.Geometry.Curvature.RestrictOpenRm04

set_option autoImplicit false
set_option linter.style.longLine false

















noncomputable section

namespace DifferentialGeometry.Integral.Connection

open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
variable [IsManifold I 1 N]
variable [T2Space N] [SigmaCompactSpace N]







omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace N] in
theorem metricRm04StdAt_pullback_localDiffeo
    (g : SmoothRiemannianMetric I N)
    (V : TopologicalSpace.Opens N) [SigmaCompactSpace V] [T2Space V]
      [BoundarylessManifold I V] [IsManifold I 1 V] [IsManifold I ((∞ : WithTop ℕ∞) + 1) V]
    (W : TopologicalSpace.Opens M) [SigmaCompactSpace W] [T2Space W]
      [BoundarylessManifold I W] [IsManifold I 1 W] [IsManifold I ((∞ : WithTop ℕ∞) + 1) W]
    (Ψ : W ≃ₘ⟮I, I⟯ V) (x : W) (X Y Z W' : TangentSpace I x) :
    metricRm04StdAt (I := I) (M := W)
        (Diffeomorph.pullbackMetric (I := I) (g.restrictOpen (I := I) V) Ψ) x X Y Z W' =
      metricRm04StdAt (I := I) (M := N) g ((Ψ x : V) : N)
        (mfderiv I I (Ψ : W → V) x X) (mfderiv I I (Ψ : W → V) x Y)
        (mfderiv I I (Ψ : W → V) x Z) (mfderiv I I (Ψ : W → V) x W') := by
  rw [metricRm04Std_pullback (I := I) (g.restrictOpen (I := I) V) Ψ x X Y Z W',
    metricRm04StdAt_restrictOpen (I := I) g V (Ψ x)
      (mfderiv I I (Ψ : W → V) x X) (mfderiv I I (Ψ : W → V) x Y)
      (mfderiv I I (Ψ : W → V) x Z) (mfderiv I I (Ψ : W → V) x W')]

end DifferentialGeometry.Integral.Connection
