import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Basic

/-!
# Coordinate balls

Chart-shape predicates and constructions, layered by how much ambient
structure they need so downstream code imports only the generality it uses:

1. **Model-generic** — `IsCoordinateBall` is stated over any metric model
   space, not just `EuclideanSpace`; it is the reusable base every other
   layer builds on.
2. **Euclidean charts** — `IsCenteredAt`, `IsCoordinateBox`, `centerAt`
   need coordinates and an origin, so they specialise to the Euclidean model.
3. **Smooth-manifold layer** — `IsSmoothCoordinateBall` and
   `IsRegularCoordinateBall` build on the maximal smooth atlas; these are the
   interface consumed by covering and partition-of-unity arguments. The
   "collar room" of a regular coordinate ball is the reusable payload; the
   predicate itself is mostly a stepping stone to
   `IsRegularCoordinateBall.exists_smoothCoordinateBall_superset`.

## Main definitions

* `OpenPartialHomeomorph.IsCoordinateBall` — the chart's image is an open metric ball.
* `OpenPartialHomeomorph.IsCenteredAt` — the chart sends the point to `0`.
* `OpenPartialHomeomorph.IsCoordinateBox` — the chart's image is a product of open intervals.
* `OpenPartialHomeomorph.centerAt` — translate a chart so a source point maps to `0`.
* `Manifold.IsSmoothCoordinateBall` — source of a maximal-atlas chart whose image is an open ball.
* `Manifold.IsRegularCoordinateBall` — a coordinate ball whose closure sits in a larger chart.

## Main results

* `OpenPartialHomeomorph.isCoordinateBall_of_target_eq_ball` — a chart with ball image is a coordinate ball.
* `OpenPartialHomeomorph.isCoordinateBox_of_target_eq` — a chart with box image is a coordinate box.
* `OpenPartialHomeomorph.centerAt_isCenteredAt` — the centered chart is centered at its point.
* `Manifold.IsRegularCoordinateBall.exists_smoothCoordinateBall_superset` — a regular
  coordinate ball lies in a surrounding smooth coordinate ball.

Provenance: SmoothManifoldsLee a5f308c — Definition_1_extra_2, Definition_1_3_extra_1.
-/

noncomputable section

open Set
open scoped Manifold Topology

universe u v

section Charts

variable {H : Type*} [PseudoMetricSpace H]
variable {n : ℕ} {M : Type u} [TopologicalSpace M]

/-- **Math.** The chart `e` is a *coordinate ball*: its image is an open metric ball
`Metric.ball c r` of positive radius. Stated over any metric model space, so it
applies beyond `EuclideanSpace`. -/
def OpenPartialHomeomorph.IsCoordinateBall (e : OpenPartialHomeomorph M H) : Prop :=
  ∃ c : H, ∃ r : ℝ, 0 < r ∧ e.target = Metric.ball c r

/-- **Math.** A chart whose image is a given open ball `Metric.ball c r` is a
coordinate ball. -/
theorem OpenPartialHomeomorph.isCoordinateBall_of_target_eq_ball
    (e : OpenPartialHomeomorph M H) (c : H) (r : ℝ) (hr : 0 < r)
    (h : e.target = Metric.ball c r) : e.IsCoordinateBall :=
  ⟨c, r, hr, h⟩

variable (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))

/-- **Math.** The chart `e` is *centered at* `p`: the point `p` lies in its source
and `e` sends it to the origin `0`. -/
def OpenPartialHomeomorph.IsCenteredAt (p : M) : Prop :=
  p ∈ e.source ∧ e p = 0

/-- **Math.** The chart `e` is a *coordinate box*: its image is a product of open
intervals `∏ᵢ (aᵢ, bᵢ)`. -/
def OpenPartialHomeomorph.IsCoordinateBox : Prop :=
  ∃ a b : EuclideanSpace ℝ (Fin n),
    (∀ i, a i < b i) ∧ e.target = { x | ∀ i : Fin n, x i ∈ Set.Ioo (a i) (b i) }

/-- **Math.** A chart whose image is a given open box `∏ᵢ (aᵢ, bᵢ)` is a coordinate
box. -/
theorem OpenPartialHomeomorph.isCoordinateBox_of_target_eq
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (a b : EuclideanSpace ℝ (Fin n))
    (hab : ∀ i, a i < b i)
    (h : e.target = { x | ∀ i : Fin n, x i ∈ Set.Ioo (a i) (b i) }) : e.IsCoordinateBox :=
  ⟨a, b, hab, h⟩

/-- **Math.** *Center* the chart `e` at a source point `p`: the chart with the same
source that sends `p` to the origin. -/
def OpenPartialHomeomorph.centerAt (p : e.source) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
  e.transHomeomorph (Homeomorph.addRight (-e p))

/-- **Math.** Centering a chart leaves its domain of definition unchanged. -/
@[simp] theorem OpenPartialHomeomorph.centerAt_source (p : e.source) :
    (e.centerAt p).source = e.source :=
  rfl

/-- **Math.** The chart obtained by centering `e` at `p` is centered at `p`. -/
theorem OpenPartialHomeomorph.centerAt_isCenteredAt (p : e.source) :
    (e.centerAt p).IsCenteredAt p := by
  exact ⟨p.2, by simp [OpenPartialHomeomorph.centerAt]⟩

end Charts

namespace Manifold

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]

/-- **Math.** A *smooth coordinate ball* is a subset `B ⊆ M` that is the source of a
chart in the maximal smooth atlas whose image is an open metric ball in the model
space `E`. -/
def IsSmoothCoordinateBall (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M] (B : Set M) : Prop :=
  ∃ φ : OpenPartialHomeomorph M E,
    φ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
      φ.source = B ∧ φ.IsCoordinateBall

/-- **Math.** A *regular coordinate ball* is a subset `B` with collar room: a
maximal-atlas chart sends `B` to an open ball of radius `r`, its closure to the
concentric closed ball of radius `r`, and the whole chart image to a strictly
larger ball of radius `r' > r`. -/
def IsRegularCoordinateBall (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M] (B : Set M) : Prop :=
  ∃ chart : OpenPartialHomeomorph M E,
    chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
      closure B ⊆ chart.source ∧
      ∃ r r' : ℝ,
        0 < r ∧
          r < r' ∧
          chart '' B = Metric.ball (0 : E) r ∧
          chart '' closure B = Metric.closedBall (0 : E) r ∧
          chart.target = Metric.ball (0 : E) r'

/-- **Math.** Every regular coordinate ball is contained in a surrounding smooth
coordinate ball — the source of its defining larger chart, which contains the
closure of `B`. -/
theorem IsRegularCoordinateBall.exists_smoothCoordinateBall_superset {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    ∃ B' : Set M, IsSmoothCoordinateBall E B' ∧ closure B ⊆ B' := by
  rcases hB with ⟨chart, hchart, hclosure, r, r', hr, hr', -, -, htarget⟩
  refine ⟨chart.source, ⟨chart, hchart, rfl, ?_⟩, hclosure⟩
  exact chart.isCoordinateBall_of_target_eq_ball (0 : E) r' (lt_trans hr hr') htarget

end Manifold
