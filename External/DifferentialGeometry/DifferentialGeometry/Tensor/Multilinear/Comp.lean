





import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section Comp

namespace ContinuousLinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {ι : Type*} [Fintype ι]

theorem compContinuousMultilinearMapL_diag_continuous :
    Continuous (fun p : M →L[𝕜] M' ↦
      (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
        ContinuousMultilinearMap 𝕜 (fun _ ↦ M') N →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ ↦ M) N))
  := by
  let φ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M →L[𝕜] M') _ :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ M) (fun _ : ι ↦ M') N
  change Continuous (fun p : M →L[𝕜] M' ↦ φ (fun _ : ι ↦ p))
  exact φ.cont.comp (continuous_pi (fun _ ↦ continuous_id))

end ContinuousLinearMap

section Continuous

variable
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (ι : Type*) [Fintype ι]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [ContinuousAdd F₁]

theorem ContinuousMultilinearMap.compContinuousLinearMapL_diag_continuous :
  Continuous (fun p : F₁ →L[𝕜] F₁ ↦
  (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
    ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂))
  := by
  let φ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁ →L[𝕜] F₁) _ :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
    𝕜 (fun _ : ι ↦ F₁) (fun _ : ι ↦ F₁) F₂
  change Continuous (fun p : F₁ →L[𝕜] F₁ ↦ φ (fun _ : ι ↦ p))
  apply Continuous.comp
  · apply ContinuousMultilinearMap.cont
  · apply continuous_pi
    intro _
    exact continuous_id

end Continuous

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
