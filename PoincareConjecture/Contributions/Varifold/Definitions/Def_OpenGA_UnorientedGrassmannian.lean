import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The Grassmannian of unoriented planes

`OpenGA.Grassmannian E k` consists of exactly the `k`-dimensional real subspaces of `E`.
The metric is the operator norm of the difference of orthogonal projections. This is the
projection model of the Grassmannian; no orientation or choice of basis is included.

Reference: Leon Simon, *Introduction to Geometric Measure Theory*, 2018 lecture notes,
Chapter 8, Section 1, pp. 235-236. Simon uses the Euclidean matrix norm of projections;
we use the operator norm, another norm on the same finite-dimensional operator space.
The compactness proof below uses the closed, bounded set of self-adjoint idempotents
of trace `k`. This is distinct from Mathlib's algebraic, quotient-rank Grassmannian.
-/

noncomputable section

open Set Topology

namespace OpenGA

/-- Unoriented `k`-planes in a finite-dimensional real inner product space. -/
def Grassmannian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k : ℕ) :=
  {S : Submodule ℝ E // Module.finrank ℝ S = k}

namespace Grassmannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {k : ℕ}

/-- The underlying plane. Its dimension is part of the definition. -/
def plane (P : Grassmannian E k) : Submodule ℝ E := P.val

@[simp] theorem finrank_plane (P : Grassmannian E k) :
    Module.finrank ℝ P.plane = k := P.property

@[ext] theorem ext {P Q : Grassmannian E k} (h : P.plane = Q.plane) : P = Q :=
  Subtype.ext h

/-- Orthogonal projection onto the plane, with values in the ambient space. -/
def projection (P : Grassmannian E k) : E →L[ℝ] E := P.plane.starProjection

theorem projection_injective : Function.Injective (projection : Grassmannian E k → E →L[ℝ] E) := by
  intro P Q h
  apply ext
  have hr := congrArg (fun A : E →L[ℝ] E => A.range) h
  simpa [projection, Submodule.range_starProjection] using hr

instance : MetricSpace (Grassmannian E k) :=
  MetricSpace.induced projection projection_injective inferInstance

theorem isometry_projection : Isometry (projection : Grassmannian E k → E →L[ℝ] E) :=
  fun _ _ => rfl

theorem continuous_projection : Continuous (projection : Grassmannian E k → E →L[ℝ] E) :=
  isometry_projection.continuous

@[simp] theorem dist_eq (P Q : Grassmannian E k) :
    dist P Q = ‖P.projection - Q.projection‖ :=
  (isometry_projection.dist_eq P Q).symm.trans (dist_eq_norm _ _)

instance : SecondCountableTopology (Grassmannian E k) :=
  isometry_projection.isEmbedding.secondCountableTopology

instance : MeasurableSpace (Grassmannian E k) := borel _
instance : BorelSpace (Grassmannian E k) := ⟨rfl⟩

theorem projection_mem (P : Grassmannian E k) (v : E) : P.projection v ∈ P.plane :=
  P.plane.starProjection_apply_mem v

@[simp] theorem projection_eq_self_iff (P : Grassmannian E k) (v : E) :
    P.projection v = v ↔ v ∈ P.plane := P.plane.starProjection_eq_self_iff

theorem norm_projection_le (P : Grassmannian E k) : ‖P.projection‖ ≤ 1 :=
  P.plane.starProjection_norm_le

theorem isStarProjection_projection (P : Grassmannian E k) : IsStarProjection P.projection :=
  isStarProjection_starProjection

theorem trace_projection (P : Grassmannian E k) :
    LinearMap.trace ℝ E P.projection.toLinearMap = k := by
  have hid := ContinuousLinearMap.IsIdempotentElem.toLinearMap
    P.plane.isIdempotentElem_starProjection
  have h := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  change LinearMap.trace ℝ E P.projection.toLinearMap =
    (Module.finrank ℝ P.plane.starProjection.range : ℝ) at h
  rw [Submodule.range_starProjection, P.finrank_plane] at h
  exact h

/-- The image of the projection representation is described by closed algebraic conditions. -/
theorem range_projection :
    Set.range (projection : Grassmannian E k → E →L[ℝ] E) =
      {A | IsStarProjection A ∧ LinearMap.trace ℝ E A.toLinearMap = k} := by
  ext A
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P.isStarProjection_projection, P.trace_projection⟩
  · rintro ⟨hA, htr⟩
    obtain ⟨_, heq⟩ := isStarProjection_iff_eq_starProjection_range.mp hA
    have hdim : Module.finrank ℝ A.range = k := by
      have hid := ContinuousLinearMap.IsIdempotentElem.toLinearMap hA.isIdempotentElem
      have ht := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
      exact_mod_cast ht.symm.trans htr
    exact ⟨⟨A.range, hdim⟩, heq.symm⟩

theorem isClosed_range_projection :
    IsClosed (Set.range (projection : Grassmannian E k → E →L[ℝ] E)) := by
  rw [range_projection]
  have htrace : Continuous (fun A : E →L[ℝ] E => LinearMap.trace ℝ E A.toLinearMap) :=
    ((LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional
  have hid : IsClosed {A : E →L[ℝ] E | A * A = A} :=
    isClosed_eq (continuous_id.mul continuous_id) continuous_id
  have hstar : IsClosed {A : E →L[ℝ] E | star A = A} :=
    isClosed_eq continuous_star continuous_id
  simpa only [isStarProjection_iff, IsIdempotentElem, IsSelfAdjoint, Set.ofPred_and] using
    (hid.inter hstar).inter (isClosed_eq htrace (continuous_const (y := (k : ℝ))))

/-- The Grassmannian is compact, including the empty case `k > dim E`. -/
instance : CompactSpace (Grassmannian E k) := by
  have hbounded : Bornology.IsBounded
      (Set.range (projection : Grassmannian E k → E →L[ℝ] E)) := by
    apply (Metric.isBounded_closedBall (x := (0 : E →L[ℝ] E)) (r := 1)).subset
    rintro A ⟨P, rfl⟩
    simpa using P.norm_projection_le
  have hc := Metric.isCompact_of_isClosed_isBounded isClosed_range_projection hbounded
  exact ⟨isometry_projection.isEmbedding.isCompact_iff.mpr (by simpa using hc)⟩

end Grassmannian
end OpenGA
