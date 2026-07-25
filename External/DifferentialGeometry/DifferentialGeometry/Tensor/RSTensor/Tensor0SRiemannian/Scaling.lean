import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Coordinate

set_option autoImplicit false
set_option linter.style.longLine false









namespace Tensor0SBundle

noncomputable section

open DifferentialGeometry
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


omit [FiniteDimensional ℝ E] in
theorem metricInvBasis_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv) :
    MetricInverseInBasis_gen (I := I) (scaleMetric (I := I) c hc g) x basis
      (fun i j => c⁻¹ * gInv i j) := by
  intro i k
  have hc0 : c ≠ 0 := ne_of_gt hc
  constructor
  · calc
      ∑ j, (c⁻¹ * gInv i j) *
          (scaleMetric (I := I) c hc g).inner x (basis j) (basis k)
          = ∑ j, gInv i j * g.inner x (basis j) (basis k) := by
            apply Finset.sum_congr rfl
            intro j _hj
            simp [scaleMetric_inner]
            field_simp [hc0]
      _ = if i = k then 1 else 0 := (hinv i k).1
  · calc
      ∑ j, (scaleMetric (I := I) c hc g).inner x (basis i) (basis j) *
          (c⁻¹ * gInv j k)
          = ∑ j, g.inner x (basis i) (basis j) * gInv j k := by
            apply Finset.sum_congr rfl
            intro j _hj
            simp [scaleMetric_inner]
            field_simp [hc0]
      _ = if i = k then 1 else 0 := (hinv i k).2


theorem normSq0S_smul
    (g : SmoothRiemannianMetric I M) {x : M} {s : Nat}
    (c : Real) (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s x) :
    normSq0S (I := I) g x s (c • A) = c ^ 2 * normSq0S (I := I) g x s A := by
  let D := tensor0SMetricData (I := I) g x s
  change D.flat (c • A) (c • A) = c ^ 2 * D.flat A A
  calc
    D.flat (c • A) (c • A) = (c • D.flat A) (c • A) := by
      rw [D.flat.map_smul]
    _ = c * D.flat A (c • A) := by rfl
    _ = c * (c * D.flat A A) := by rw [(D.flat A).map_smul]; rfl
    _ = c ^ 2 * D.flat A A := by ring



theorem normSq0S_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    {x : M} (s : Nat) (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s x) :
    normSq0S (I := I) (scaleMetric (I := I) c hc g) x s A =
      (c⁻¹) ^ s * normSq0S (I := I) g x s A := by
  classical
  let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx
      (𝕜 := Real) E) Real (TangentSpace I x) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x k l (extChartAt I x x)
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x
  have hinvScale :
      MetricInverseInBasis_gen (I := I) (scaleMetric (I := I) c hc g) x basis
        (fun i j => c⁻¹ * gInv i j) :=
    metricInvBasis_scale (I := I) c hc g basis gInv hinv
  rw [normSq0S_eq_coord (I := I) (scaleMetric (I := I) c hc g) x s basis
      (fun i j => c⁻¹ * gInv i j) hinvScale A,
    normSq0S_eq_coord (I := I) g x s basis gInv hinv A]
  unfold coordInner0S
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring



theorem normSq0S_two_scale
    (c : Real) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    {x : M} (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 x) :
    normSq0S (I := I) (scaleMetric (I := I) c hc g) x 2 A =
      c⁻¹ * c⁻¹ * normSq0S (I := I) g x 2 A := by
  classical
  let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)
      Real (TangentSpace I x) :=
    DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
  let gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
    fun k l =>
      DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
        (I := I) g x k l (extChartAt I x x)
  have hinv : MetricInverseInBasis_gen (I := I) g x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x
  have hinvScale :
      MetricInverseInBasis_gen (I := I) (scaleMetric (I := I) c hc g) x basis
        (fun i j => c⁻¹ * gInv i j) :=
    metricInvBasis_scale (I := I) c hc g basis gInv hinv
  rw [normSq0S_two_eq_coord (I := I) (scaleMetric (I := I) c hc g) x basis
      (fun i j => c⁻¹ * gInv i j) hinvScale A,
    normSq0S_two_eq_coord (I := I) g x basis gInv hinv A]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro l _hl
  ring

end

end Tensor0SBundle
