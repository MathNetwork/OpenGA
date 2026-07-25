import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Analysis.Calculus.Deriv.Basic


open scoped Manifold ContDiff

namespace DifferentialGeometry

theorem contMDiff_partial_deriv_fst
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (F : C^∞⟮𝓘(ℝ, ℝ).prod I, ℝ × M; ℝ⟯) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => deriv (fun t => F (t, p.2)) p.1) := by

  have hrw : (fun p : ℝ × M => deriv (fun t => F (t, p.2)) p.1) =
      fun p : ℝ × M => (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t => F (t, p.2)) p.1) (1 : ℝ) := by
    funext p
    rw [mfderiv_eq_fderiv]
    exact (fderiv_apply_one_eq_deriv (f := fun t => F (t, p.2)) (x := p.1)).symm
  rw [hrw]

  rw [contMDiff_infty]
  intro n p₀

  have harg : ContMDiff ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : (ℝ × M) × ℝ => (q.2, q.1.2)) :=
    ContMDiff.prodMk contMDiff_snd contMDiff_fst.snd
  have hF : ContMDiff ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : (ℝ × M) × ℝ => F (q.2, q.1.2)) :=
    F.contMDiff.comp harg

  have h_apply :=
    ContMDiffAt.mfderiv_apply
      (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (f := fun (p : ℝ × M) (t : ℝ) => F (t, p.2))
      (g := fun p : ℝ × M => p.1)
      (g₁ := fun p : ℝ × M => p)
      (g₂ := fun _ : ℝ × M => (1 : ℝ))
      (x₀ := p₀)
      (m := (n : WithTop ℕ∞))
      ((hF.of_le (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ ∞)).contMDiffAt)
      contMDiffAt_fst
      contMDiffAt_id
      contMDiffAt_const
      le_rfl

  simpa [inTangentCoordinates_model_space] using h_apply

end DifferentialGeometry
