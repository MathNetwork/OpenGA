import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Constructions

noncomputable section

open scoped ContDiff Topology

namespace DifferentialGeometry.Analysis.BanachAlgebraSmoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem contDiffOn_ringInverse_comp {s : Set E} {g : E → A} {n : WithTop ℕ∞}
    (hg : ContDiffOn ℝ n g s) (hunit : ∀ x ∈ s, IsUnit (g x)) :
    ContDiffOn ℝ n (fun x => Ring.inverse (g x)) s := by
  have hinv : ContDiffOn ℝ n Ring.inverse {y : A | IsUnit y} := by
    intro y hy
    exact (contDiffAt_ringInverse ℝ (IsUnit.unit hy)).contDiffWithinAt
  exact hinv.comp hg (fun x hx => hunit x hx)

theorem contDiffOn_oneSub_inverse_comp {s : Set E} {g : E → A} {n : WithTop ℕ∞}
    (hg : ContDiffOn ℝ n g s) (hlt : ∀ x ∈ s, ‖g x‖ < 1) :
    ContDiffOn ℝ n (fun x => Ring.inverse (1 - g x)) s := by
  refine contDiffOn_ringInverse_comp (contDiffOn_const.sub hg) (fun x hx => ?_)
  exact (Units.oneSub (g x) (hlt x hx)).isUnit

theorem contDiffOn_oneSub_inverse_clm {s : Set E} {L : E →L[ℝ] A} {n : WithTop ℕ∞}
    (hlt : ∀ x ∈ s, ‖L x‖ < 1) :
    ContDiffOn ℝ n (fun x => Ring.inverse (1 - L x)) s :=
  contDiffOn_oneSub_inverse_comp L.contDiff.contDiffOn hlt

theorem contDiffOn_oneSub_inverse_clm_mul_const {s : Set E} {L : E →L[ℝ] A} {c : A}
    {n : WithTop ℕ∞} (hlt : ∀ x ∈ s, ‖L x‖ < 1) :
    ContDiffOn ℝ n (fun x => Ring.inverse (1 - L x) * c) s :=
  (contDiffOn_oneSub_inverse_clm hlt).mul contDiffOn_const

theorem contDiffOn_continuousLinearMap_comp_oneSub_inverse_clm
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} {L : E →L[ℝ] A} {c : A} (Φ : A →L[ℝ] F) {n : WithTop ℕ∞}
    (hlt : ∀ x ∈ s, ‖L x‖ < 1) :
    ContDiffOn ℝ n (fun x => Φ (Ring.inverse (1 - L x) * c)) s :=
  (contDiffOn_oneSub_inverse_clm_mul_const hlt).continuousLinearMap_comp Φ

omit [CompleteSpace A] in

theorem contDiffOn_bilinDiag {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set E} {B : A × A → G} {f h : E → A} {n : WithTop ℕ∞}
    (hB : IsBoundedBilinearMap ℝ B) (hf : ContDiffOn ℝ n f s) (hh : ContDiffOn ℝ n h s) :
    ContDiffOn ℝ n (fun x => B (f x, h x)) s :=
  hB.contDiff.comp_contDiffOn (hf.prodMk hh)

end DifferentialGeometry.Analysis.BanachAlgebraSmoothness

end
