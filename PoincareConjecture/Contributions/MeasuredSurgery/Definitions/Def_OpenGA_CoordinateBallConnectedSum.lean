import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Constructions

/-!
# Connected sums by gluing punctured coordinate balls

The definition uses an actual quotient space: remove an open coordinate ball
from each manifold and identify the two boundary spheres by a homeomorphism.
The coordinate charts contain the closed balls in their open sources, so the
boundaries have collars; arbitrary wild embedded balls are not allowed.

Only the topological connected sum is defined here. Orientations, smooth
structures on the quotient, independence of the choices, and the van Kampen
theorem for this construction are separate results.
-/

namespace OpenGA

abbrev EuclideanThree := EuclideanSpace ℝ (Fin 3)
abbrev SphereTwo := ↥(Metric.sphere (0 : EuclideanThree) 1)
abbrev SphereThree := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1)
abbrev SphereOne := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)

universe u

/-- A coordinate chart defined on a neighborhood of the closed unit ball. -/
structure CoordinateBall (M : Type u) [TopologicalSpace M] where
  chart : OpenPartialHomeomorph EuclideanThree M
  closedBall_subset_source : Metric.closedBall 0 1 ⊆ chart.source

namespace CoordinateBall

variable {M : Type u} [TopologicalSpace M]

/-- The manifold with the open coordinate ball removed. -/
def Punctured (B : CoordinateBall M) := ↥((B.chart '' Metric.ball 0 1)ᶜ)

instance (B : CoordinateBall M) : TopologicalSpace B.Punctured :=
  inferInstanceAs (TopologicalSpace ↥((B.chart '' Metric.ball 0 1)ᶜ))

/-- Boundary points remain in the punctured manifold. -/
def boundary (B : CoordinateBall M) (x : SphereTwo) : B.Punctured := by
  refine ⟨B.chart x, ?_⟩
  rintro ⟨y, hy, heq⟩
  have hxy : y = (x : EuclideanThree) := B.chart.injOn
    (B.closedBall_subset_source (Metric.ball_subset_closedBall hy))
    (B.closedBall_subset_source (Metric.sphere_subset_closedBall x.property)) heq
  have hdist := Metric.mem_sphere.mp x.property
  have hlt := Metric.mem_ball.mp hy
  rw [hxy, hdist] at hlt
  exact lt_irrefl _ hlt

end CoordinateBall

namespace ConnectedSum

variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]

/-- The generating identifications, before taking equivalence closure. -/
def BoundaryIdentification (B : CoordinateBall M) (C : CoordinateBall N)
    (glue : SphereTwo ≃ₜ SphereTwo) :
    (B.Punctured ⊕ C.Punctured) → (B.Punctured ⊕ C.Punctured) → Prop :=
  fun a b => ∃ x : SphereTwo,
    a = Sum.inl (B.boundary x) ∧ b = Sum.inr (C.boundary (glue x))

/-- Gluing two punctured manifolds along their entire boundary spheres.
`Quot` takes the equivalence closure, and its topology is the quotient topology. -/
def Space (B : CoordinateBall M) (C : CoordinateBall N)
    (glue : SphereTwo ≃ₜ SphereTwo) := Quot (BoundaryIdentification B C glue)

instance (B : CoordinateBall M) (C : CoordinateBall N) (glue : SphereTwo ≃ₜ SphereTwo) :
    TopologicalSpace (Space B C glue) :=
  inferInstanceAs (TopologicalSpace (Quot (BoundaryIdentification B C glue)))

end ConnectedSum

/-- `X` is a topological connected sum of `M` and `N`, witnessed by coordinate
balls, a boundary gluing map, and a homeomorphism to the resulting quotient. -/
def IsConnectedSum (M N X : Type u)
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace X] : Prop :=
  ∃ (B : CoordinateBall M) (C : CoordinateBall N) (glue : SphereTwo ≃ₜ SphereTwo),
    Nonempty (X ≃ₜ ConnectedSum.Space B C glue)

end OpenGA
