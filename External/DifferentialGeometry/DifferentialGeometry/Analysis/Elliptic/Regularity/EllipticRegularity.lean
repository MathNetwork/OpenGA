import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SmoothWeakSolutionH2
import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Geometry.Operator.Laplacian


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace EllipticRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

def chartLocalEuclideanForm
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :
    DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm
      (Module.finrank ℝ E) Ω where
  a := fun _ => (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
  c := fun _ => 0
  symm := by
    intro _ i j
    by_cases hij : i = j
    · subst hij; rfl
    · simp [hij, Ne.symm hij]
  smooth_a := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have hone : (fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) i i) =
          (fun _ => (1 : ℝ)) := by
        funext _
        simp
      rw [hone]
      exact contDiff_const
    · have hzero : (fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) i j) =
          (fun _ => (0 : ℝ)) := by
        funext _
        simp [hij]
      rw [hzero]
      exact contDiff_const
  smooth_c := contDiff_const
  lam := 1
  capLam := 1
  hlam_pos := by norm_num
  hlam_le_capLam := le_refl _
  coercive := by
    intro x _hx ξ
    have h_id_action :
        DeGiorgi.matMulE
          (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) ξ = ξ := by
      ext i
      rw [DeGiorgi.matMulE_apply]
      rw [Matrix.one_mulVec]
    rw [h_id_action]
    rw [one_mul, real_inner_self_eq_norm_mul_norm, sq]

omit [FiniteDimensional ℝ E] in
@[simp] lemma chartLocalEuclideanForm_a_apply
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    (chartLocalEuclideanForm (E := E) Ω).a x =
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := rfl

omit [FiniteDimensional ℝ E] in
@[simp] lemma chartLocalEuclideanForm_c_apply
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    (chartLocalEuclideanForm (E := E) Ω).c x = 0 := rfl

omit [FiniteDimensional ℝ E] in
@[simp] lemma chartLocalEuclideanForm_lam
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :
    (chartLocalEuclideanForm (E := E) Ω).lam = 1 := rfl

omit [FiniteDimensional ℝ E] in
@[simp] lemma chartLocalEuclideanForm_capLam
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :
    (chartLocalEuclideanForm (E := E) Ω).capLam = 1 := rfl

omit [FiniteDimensional ℝ E] in
theorem chartLocalEuclideanForm_principalIntegrand
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (u v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand
      (chartLocalEuclideanForm (E := E) Ω) u v x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          ((fderiv ℝ v x) (EuclideanSpace.single i 1)) := by
  classical
  unfold DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [chartLocalEuclideanForm_a_apply]
  · intro j _ hji
    have h1 : (chartLocalEuclideanForm (E := E) Ω).a x i j = 0 := by
      rw [chartLocalEuclideanForm_a_apply]
      simp [hji.symm]
    rw [h1]; ring
  · intro hk
    exact absurd (Finset.mem_univ i) hk

omit [FiniteDimensional ℝ E] in
theorem chartLocalEuclideanForm_principalIntegrand_self
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand
      (chartLocalEuclideanForm (E := E) Ω) u u x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2 := by
  rw [chartLocalEuclideanForm_principalIntegrand]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [sq]

omit [FiniteDimensional ℝ E] in
theorem chartLocalEuclideanForm_principalIntegrand_self_eq_gradient_sq
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand
      (chartLocalEuclideanForm (E := E) Ω) u u x =
      ‖DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.gradientVec
        (chartLocalEuclideanForm (E := E) Ω) u x‖ ^ 2 := by
  rw [chartLocalEuclideanForm_principalIntegrand_self]
  rw [DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.gradientVec_norm_sq_eq_sum]

omit [FiniteDimensional ℝ E] in
theorem chartLocalEuclideanForm_bilin
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (u v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bilin
      (chartLocalEuclideanForm (E := E) Ω) u v =
      ∫ x in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            ((fderiv ℝ v x) (EuclideanSpace.single i 1)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
  unfold DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bilin
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  change DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand
      (chartLocalEuclideanForm (E := E) Ω) u v x +
      (chartLocalEuclideanForm (E := E) Ω).c x * u x * v x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          ((fderiv ℝ v x) (EuclideanSpace.single i 1))
  rw [chartLocalEuclideanForm_principalIntegrand, chartLocalEuclideanForm_c_apply]
  ring

end EllipticRegularity
end Laplacian
end Analysis
end DifferentialGeometry
