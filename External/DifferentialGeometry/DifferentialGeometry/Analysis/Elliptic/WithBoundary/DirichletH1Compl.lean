import DifferentialGeometry.Analysis.Elliptic.WithBoundary.InteriorSmoothBridge

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary
namespace Dirichlet

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

open DifferentialGeometry.Integral.Measure

abbrev SmoothScalarDirichlet (g : SmoothRiemannianMetric (I_half n) M) :=
  InteriorSmoothScalar g

abbrev H1ComplDirichlet (g : SmoothRiemannianMetric (I_half n) M) :=
  H1ComplInterior g

theorem H1ComplDirichlet_eq_completion (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplDirichlet g = UniformSpace.Completion (SmoothScalarDirichlet g) := rfl

noncomputable def smoothToH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M) :
    SmoothScalarDirichlet g →L[ℝ] H1ComplDirichlet g :=
  smoothToH1ComplInterior g

theorem denseRange_smoothToH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M) :
    DenseRange (smoothToH1ComplDirichlet g) := by
  change DenseRange (UniformSpace.Completion.toComplL :
      SmoothScalarDirichlet g →L[ℝ] H1ComplDirichlet g)
  rw [show (UniformSpace.Completion.toComplL :
      SmoothScalarDirichlet g → H1ComplDirichlet g) =
      ((↑) : SmoothScalarDirichlet g →
        UniformSpace.Completion (SmoothScalarDirichlet g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

noncomputable def smoothToLpDirichlet (g : SmoothRiemannianMetric (I_half n) M) :
    SmoothScalarDirichlet g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  smoothToLpInterior g

noncomputable def H1ComplDirichletToLp (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplDirichlet g →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) :=
  H1ComplInteriorToLp g

@[simp] lemma H1ComplDirichletToLp_smoothToH1ComplDirichlet
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : SmoothScalarDirichlet g) :
    H1ComplDirichletToLp g (smoothToH1ComplDirichlet g f) =
      smoothToLpDirichlet g f :=
  H1ComplInteriorToLp_smoothToH1ComplInterior g f

noncomputable def resolventDirichlet
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplDirichlet g :=
  resolventInterior g

theorem resolventDirichlet_inner_eq_lpFunctional
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (v : H1ComplDirichlet g) :
    ⟪resolventDirichlet g f, v⟫_ℝ = ⟪H1ComplDirichletToLp g v, f⟫_ℝ :=
  resolventInterior_inner_eq_lpFunctional g f v

theorem smoothToH1ComplDirichlet_eq_resolventDirichlet_oneSubLap
    {g : SmoothRiemannianMetric (I_half n) M}
    (u : SmoothScalarDirichlet g) :
    smoothToH1ComplDirichlet g u = resolventDirichlet g u.oneSubLapClassicalLp :=
  smoothToH1ComplInterior_eq_resolventInterior_oneSubLap u

example (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplDirichlet g :=
  resolventDirichlet g

end Dirichlet
end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
