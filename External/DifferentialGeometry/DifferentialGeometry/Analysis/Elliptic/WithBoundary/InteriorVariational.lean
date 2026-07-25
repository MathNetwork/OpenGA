import DifferentialGeometry.Analysis.Elliptic.WithBoundary.InteriorH1Compl
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

open DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace (EuclideanSpace ℝ (Fin n)) :=
  borel _
private local instance : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

noncomputable def H1ComplInteriorBilin
    (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplInterior g →L[ℝ] H1ComplInterior g →L[ℝ] ℝ :=
  innerSL ℝ

@[simp] lemma H1ComplInteriorBilin_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (u v : H1ComplInterior g) :
    H1ComplInteriorBilin g u v = ⟪u, v⟫_ℝ := rfl

lemma H1ComplInteriorBilin_isCoercive
    (g : SmoothRiemannianMetric (I_half n) M) :
    IsCoercive (H1ComplInteriorBilin g) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro u
  rw [one_mul]
  rw [show H1ComplInteriorBilin g u u = ⟪u, u⟫_ℝ from rfl]
  rw [real_inner_self_eq_norm_sq]
  ring_nf
  exact le_refl _

noncomputable def lpFunctionalCLMInterior
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      (H1ComplInterior g →L[ℝ] ℝ) :=
  let applyL : (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ] ℝ) →L[ℝ]
      (H1ComplInterior g →L[ℝ]
        Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) →L[ℝ]
        (H1ComplInterior g →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ (H1ComplInterior g)
      (Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g)) ℝ
  ((applyL.flip) (H1ComplInteriorToLp g)).comp
    (innerSL ℝ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ] ℝ)

@[simp] lemma lpFunctionalCLMInterior_apply
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (v : H1ComplInterior g) :
    lpFunctionalCLMInterior g f v =
      ⟪H1ComplInteriorToLp g v, f⟫_ℝ := by
  change (innerSL ℝ f) (H1ComplInteriorToLp g v) =
    ⟪H1ComplInteriorToLp g v, f⟫_ℝ
  rw [innerSL_apply_apply]
  exact real_inner_comm (H1ComplInteriorToLp g v) f

noncomputable def H1ComplInteriorLaxMilgramEquiv
    (g : SmoothRiemannianMetric (I_half n) M) :
    H1ComplInterior g ≃L[ℝ] H1ComplInterior g :=
  IsCoercive.continuousLinearEquivOfBilin
    (H1ComplInteriorBilin_isCoercive g)

@[simp] lemma H1ComplInteriorLaxMilgramEquiv_apply
    (g : SmoothRiemannianMetric (I_half n) M) (u w : H1ComplInterior g) :
    ⟪H1ComplInteriorLaxMilgramEquiv g u, w⟫_ℝ = ⟪u, w⟫_ℝ :=
  IsCoercive.continuousLinearEquivOfBilin_apply _ u w

noncomputable def H1ComplInteriorRieszRepr
    (g : SmoothRiemannianMetric (I_half n) M) :
    (H1ComplInterior g →L[ℝ] ℝ) →L[ℝ] H1ComplInterior g :=
  LinearMap.mkContinuous
    { toFun := fun φ => (InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm φ
      map_add' := fun φ ψ =>
        (InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm.map_add φ ψ
      map_smul' := fun c φ => by
        change (InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm (c • φ) =
          c • (InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm φ
        rw [LinearIsometryEquiv.map_smulₛₗ
          (InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm c φ]
        rfl }
    1 (fun φ => by
      change ‖(InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm φ‖ ≤ 1 * ‖φ‖
      rw [one_mul]
      exact le_of_eq
        ((InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm.norm_map φ))

lemma H1ComplInteriorRieszRepr_inner
    (g : SmoothRiemannianMetric (I_half n) M)
    (φ : H1ComplInterior g →L[ℝ] ℝ) (w : H1ComplInterior g) :
    ⟪H1ComplInteriorRieszRepr g φ, w⟫_ℝ = φ w := by
  change ⟪(InnerProductSpace.toDual ℝ (H1ComplInterior g)).symm φ, w⟫_ℝ = φ w
  exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := H1ComplInterior g)
    (x := w) (y := φ)

noncomputable def resolventInterior
    (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplInterior g :=
  (H1ComplInteriorRieszRepr g).comp (lpFunctionalCLMInterior g)

theorem resolventInterior_inner_eq_lpFunctional
    (g : SmoothRiemannianMetric (I_half n) M)
    (f : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g))
    (v : H1ComplInterior g) :
    ⟪resolventInterior g f, v⟫_ℝ =
      ⟪H1ComplInteriorToLp g v, f⟫_ℝ := by
  unfold resolventInterior
  rw [ContinuousLinearMap.comp_apply, H1ComplInteriorRieszRepr_inner,
    lpFunctionalCLMInterior_apply]

example (g : SmoothRiemannianMetric (I_half n) M) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) g) →L[ℝ]
      H1ComplInterior g :=
  resolventInterior g

end WithBoundary
end Laplacian
end Analysis
end DifferentialGeometry

end
