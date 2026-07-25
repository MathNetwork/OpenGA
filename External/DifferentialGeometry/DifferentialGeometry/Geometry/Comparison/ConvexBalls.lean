import DifferentialGeometry.Geometry.Comparison.GeodesicConvexity
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

set_option autoImplicit false


























open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [T2Space (TangentBundle I M)]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]












omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] in
theorem isConvexWith_smallNormalBall
    (join : M → M → ℝ → M) (O : M) {r : ℝ}
    (hjoin : ∀ a ∈ smallNormalBall (I := I) O r, ∀ b ∈ smallNormalBall (I := I) O r,
      ContinuousOn (join a b) unitInterval ∧ join a b 0 = a ∧ join a b 1 = b)
    (hconv : ∀ a ∈ smallNormalBall (I := I) O r, ∀ b ∈ smallNormalBall (I := I) O r,
      ConvexOn ℝ unitInterval
        (fun t => (riemannianEDist I O (join a b t)).toReal ^ 2)) :
    IsGeodesicallyConvexWith join (smallNormalBall (I := I) O r) := by
  intro a ha b hb
  obtain ⟨hcont, h0, h1⟩ := hjoin a ha b hb
  refine ⟨hcont, h0, h1, fun t ht => ?_⟩
  have hane : riemannianEDist I O a ≠ ⊤ := riemannianEDist_ne_top (I := I) O a
  have hbne : riemannianEDist I O b ≠ ⊤ := riemannianEDist_ne_top (I := I) O b
  have hta : (riemannianEDist I O a).toReal < r :=
    (ENNReal.lt_ofReal_iff_toReal_lt hane).mp ha
  have htb : (riemannianEDist I O b).toReal < r :=
    (ENNReal.lt_ofReal_iff_toReal_lt hbne).mp hb

  have hseg : t ∈ segment ℝ (0 : ℝ) (1 : ℝ) := by
    rw [segment_eq_Icc zero_le_one]; exact ht
  have hmax := (hconv a ha b hb).le_on_segment
    unitInterval.zero_mem unitInterval.one_mem hseg
  rw [h0, h1] at hmax

  have htR : (0 : ℝ) ≤ (riemannianEDist I O (join a b t)).toReal :=
    ENNReal.toReal_nonneg
  have htaR : (0 : ℝ) ≤ (riemannianEDist I O a).toReal := ENNReal.toReal_nonneg
  have htbR : (0 : ℝ) ≤ (riemannianEDist I O b).toReal := ENNReal.toReal_nonneg
  have hlt : (riemannianEDist I O (join a b t)).toReal < r := by
    rcases le_max_iff.mp hmax with hcase | hcase <;> nlinarith
  exact (ENNReal.lt_ofReal_iff_toReal_lt
    (riemannianEDist_ne_top (I := I) O (join a b t))).mpr hlt

end Riemannian
end Geometry
end DifferentialGeometry
