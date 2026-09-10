import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

noncomputable section Comp

section Smooth

variable {𝕜 ι F₁ F₂} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]

theorem ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff :
  ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁ ↦
  (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂))
  := by
  let φ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁ →L[𝕜] F₁) _ :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ F₁) (fun _ : ι ↦ F₁) F₂
  change ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁ ↦ φ (fun _ : ι ↦ p))
  rw [show (fun p : F₁ →L[𝕜] F₁ => φ (fun _ : ι => p)) =
    (φ : (ι → (F₁ →L[𝕜] F₁)) → _) ∘ (fun p : F₁ →L[𝕜] F₁ => (fun _ : ι => p)) from rfl]
  exact (ContinuousMultilinearMap.contDiff φ).comp
    (contDiff_pi.2 (fun _ => contDiff_id))

end Smooth

end Comp
