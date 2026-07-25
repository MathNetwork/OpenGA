import DifferentialGeometry.Geometry.Comparison.CenterOfMass

set_option autoImplicit false
set_option linter.style.longLine false










noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]







structure StrictDistInput (g : SmoothRiemannianMetric I M)
    {ι : Type} [Fintype ι] (pts : ι → M)
    (join : M → M → ℝ → M) (p : M) (r : ℝ) : Prop where
  mid :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ a ∈ Metric.closedBall p (2 * r), ∀ b ∈ Metric.closedBall p (2 * r),
      a ≠ b → join a b (1 / 2 : ℝ) ∈ Metric.closedBall p (2 * r)
  zero :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ a ∈ Metric.closedBall p (2 * r), ∀ b ∈ Metric.closedBall p (2 * r),
      join a b 0 = a
  one :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ a ∈ Metric.closedBall p (2 * r), ∀ b ∈ Metric.closedBall p (2 * r),
      join a b 1 = b
  strict :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    letI : MetricSpace M := HopfRinow.riemMetricSpace (I := I) (M := M)
    ∀ i : ι, ∀ a ∈ Metric.closedBall p (2 * r),
      ∀ b ∈ Metric.closedBall p (2 * r), a ≠ b →
        StrictConvexOn ℝ unitInterval
          (fun t : ℝ => CenterOfMass.halfSqDist (pts i) (join a b t))

end HCGCompactness
end DifferentialGeometry
