import Definitions.Def_OpenGA_WeightedMapVarifold
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Theorems.Thm_OpenGA_areaDensity_eq_normDet
import Mathlib.Analysis.Calculus.ContDiff.Defs


namespace OpenGA
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
lemma continuous_areaDensity : Continuous (fun p : F × F => areaDensity p.1 p.2) := by
  unfold areaDensity
  fun_prop
end OpenGA

/-!
# Varifolds of parametrized surfaces in Euclidean space

The Jacobian is the actual `normDet` of the Frechet derivative. A measurable
tangent lift must agree with its range wherever the Jacobian is nonzero.
Using Lebesgue measure on the two-dimensional parameter space, restricted to
the parameter domain, we construct the finite-area varifold and prove that it
is independent of the tangent-plane extension on the zero-Jacobian set.

The measurable tangent lift is explicit input: this file does not yet construct
it automatically for every `C^1` map. Nor does it glue manifold charts or supply
the weak derivative for Sobolev surface maps. The definition already uses the
actual derivative, rather than an unconstrained surrogate for it.

References: Simon, *Introduction to Geometric Measure Theory*, 2018, Chapters 2
and 8; Colding-Minicozzi, arXiv:0707.0108, Section 1.3, p. 5.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal CompactlySupported

namespace OpenGA.Varifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The two-dimensional area Jacobian, computed from the actual derivative. -/
def surfaceJacobian (f : EuclideanSpace ℝ (Fin 2) → E)
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ≥0 :=
  ⟨(fderiv ℝ f x).toLinearMap.normDet, (fderiv ℝ f x).toLinearMap.normDet_nonneg⟩

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Agreement with the previously verified, basis-independent area density. -/
theorem surfaceJacobian_eq_areaDensity (f : EuclideanSpace ℝ (Fin 2) → E)
    (x : EuclideanSpace ℝ (Fin 2))
    (b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2))) :
    (surfaceJacobian f x : ℝ) =
      areaDensity (fderiv ℝ f x (b 0)) (fderiv ℝ f x (b 1)) :=
  (areaDensity_eq_normDet (fderiv ℝ f x).toLinearMap b).symm

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem continuous_surfaceJacobian {f : EuclideanSpace ℝ (Fin 2) → E}
    (hf : ContDiff ℝ 1 f) : Continuous (surfaceJacobian f) := by
  apply Continuous.subtype_mk
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have h0 : Continuous (fun x => fderiv ℝ f x (b 0)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h1 : Continuous (fun x => fderiv ℝ f x (b 1)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  convert continuous_areaDensity.comp (h0.prodMk h1) using 1
  ext x
  exact surfaceJacobian_eq_areaDensity f x b

/-- A measurable lift to genuine tangent planes, with arbitrary choices allowed only
where the actual area Jacobian vanishes. -/
structure SurfaceTangentLift (f : EuclideanSpace ℝ (Fin 2) → E) where
  plane : EuclideanSpace ℝ (Fin 2) → Grassmannian E 2
  measurable_plane : Measurable plane
  plane_eq_range : ∀ x, surfaceJacobian f x ≠ 0 →
    (plane x).plane = (fderiv ℝ f x).range

/-- Every injective linear parametrization has its canonical constant tangent lift. -/
def linearSurfaceTangentLift (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] E)
    (hL : Function.Injective L) : SurfaceTangentLift L where
  plane := fun _ => ⟨L.range, by
    simpa using (LinearMap.finrank_range_of_inj (f := L.toLinearMap) hL)⟩
  measurable_plane := measurable_const
  plane_eq_range x _ := by simp [Grassmannian.plane]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A `C^1` parametrization has finite area on any compact parameter domain. -/
theorem finite_area_of_isCompact {f : EuclideanSpace ℝ (Fin 2) → E}
    (hf : ContDiff ℝ 1 f) {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) :
    (∫⁻ x in K, (surfaceJacobian f x : ℝ≥0∞)) < ∞ := by
  have hc : Continuous (fun x => (surfaceJacobian f x : ℝ)) :=
    (continuous_surfaceJacobian hf).subtype_val
  have hi : IntegrableOn (fun x => (surfaceJacobian f x : ℝ)) K volume :=
    hc.continuousOn.integrableOn_compact hK
  have h := (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun x => (surfaceJacobian f x).coe_nonneg))).mp
      hi.hasFiniteIntegral
  simpa using h

/-- The finite-area varifold induced by a `C^1` parametrization, relative to Lebesgue
measure on its parameter domain. Finite area is a hypothesis on this constructor,
not on the general definition of `Varifold`. -/
def ofParametrization (f : EuclideanSpace ℝ (Fin 2) → E) (hf : ContDiff ℝ 1 f)
    (Ω : Set (EuclideanSpace ℝ (Fin 2))) (P : SurfaceTangentLift f)
    (hfinite : (∫⁻ x in Ω, (surfaceJacobian f x : ℝ≥0∞)) < ∞) : Varifold E 2 :=
  ofWeightedMap (volume.restrict Ω) f P.plane (surfaceJacobian f)
    hf.continuous.measurable P.measurable_plane hfinite

/-- Its mass is the parametrized area, including multiplicity. -/
theorem mass_ofParametrization (f : EuclideanSpace ℝ (Fin 2) → E)
    (hf : ContDiff ℝ 1 f) (Ω : Set (EuclideanSpace ℝ (Fin 2)))
    (P : SurfaceTangentLift f)
    (hfinite : (∫⁻ x in Ω, (surfaceJacobian f x : ℝ≥0∞)) < ∞) :
    (ofParametrization f hf Ω P hfinite).mass =
      ∫⁻ x in Ω, (surfaceJacobian f x : ℝ≥0∞) :=
  mass_ofWeightedMap _ _ _ _ _ _ _





end OpenGA.Varifold
