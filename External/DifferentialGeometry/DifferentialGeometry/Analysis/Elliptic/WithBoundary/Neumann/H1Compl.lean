import DifferentialGeometry.Analysis.Elliptic.WithBoundary.InteriorSmoothBridge

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Neumann

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

open DifferentialGeometry.Integral.Measure

abbrev SmoothScalarNeumann (g : SmoothRiemannianMetric (I_half n) M) :=
  InteriorSmoothScalar g

abbrev H1ComplNeumann (g : SmoothRiemannianMetric (I_half n) M) :=
  H1ComplInterior g

noncomputable def smoothToH1ComplNeumann
    (g : SmoothRiemannianMetric (I_half n) M) :
    SmoothScalarNeumann g →L[ℝ] H1ComplNeumann g :=
  smoothToH1ComplInterior g

noncomputable def smoothToLpNeumann (g : SmoothRiemannianMetric (I_half n) M) :
    SmoothScalarNeumann g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  smoothToLpInterior g

noncomputable def H1ComplNeumannToLp (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplNeumann g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  H1ComplInteriorToLp g

@[simp] lemma H1ComplNeumannToLp_smoothToH1ComplNeumann
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : SmoothScalarNeumann g) :
    H1ComplNeumannToLp g (smoothToH1ComplNeumann g f) = smoothToLpNeumann g f :=
  H1ComplInteriorToLp_smoothToH1ComplInterior g f

noncomputable def resolventNeumann
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplNeumann g :=
  resolventInterior g

theorem resolventNeumann_inner_eq_lpFunctional
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (v : H1ComplNeumann g) :
    ⟪resolventNeumann g f, v⟫_ℝ = ⟪H1ComplNeumannToLp g v, f⟫_ℝ :=
  resolventInterior_inner_eq_lpFunctional g f v

theorem smoothToH1ComplNeumann_eq_resolventNeumann_oneSubLap
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : SmoothScalarNeumann g) :
    smoothToH1ComplNeumann g u = resolventNeumann g u.oneSubLapClassicalLp :=
  smoothToH1ComplInterior_eq_resolventInterior_oneSubLap u

example (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplNeumann g :=
  resolventNeumann g

end Neumann
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
