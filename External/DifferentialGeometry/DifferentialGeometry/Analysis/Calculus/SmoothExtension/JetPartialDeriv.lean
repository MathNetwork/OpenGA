import DifferentialGeometry.Analysis.Calculus.SmoothExtension.ChartRicciJet












noncomputable section

open scoped ContDiff

namespace DifferentialGeometry
namespace Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}


def matEntryCLM (l m : Fin n) : (Fin n → Fin n → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) m).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℝ) l)

@[simp] theorem matEntryCLM_apply (l m : Fin n) (M : Fin n → Fin n → ℝ) :
    matEntryCLM l m M = M l m := rfl




theorem fderiv_matEntry {G : E → (Fin n → Fin n → ℝ)} {y : E} (hG : DifferentiableAt ℝ G y)
    (v : E) (l m : Fin n) :
    (fderiv ℝ G y) v l m = fderiv ℝ (fun w => G w l m) y v := by
  have hL : fderiv ℝ (fun w => G w l m) y = (matEntryCLM l m).comp (fderiv ℝ G y) :=
    ((matEntryCLM l m).hasFDerivAt.comp y hG.hasFDerivAt).fderiv
  rw [hL]
  rfl





theorem fderiv2_matEntry {G : E → (Fin n → Fin n → ℝ)} {y : E}
    (hG : DifferentiableAt ℝ (fun w => fderiv ℝ G w) y) (u v : E) (l m : Fin n) :
    ((fderiv ℝ (fun w => fderiv ℝ G w) y) u) v l m
      = fderiv ℝ (fun w => (fderiv ℝ G w) v l m) y u := by
  have hL : fderiv ℝ (fun w => (fderiv ℝ G w) v l m) y
      = ((matEntryCLM l m).comp (ContinuousLinearMap.apply ℝ (Fin n → Fin n → ℝ) v)).comp
          (fderiv ℝ (fun w => fderiv ℝ G w) y) :=
    (((matEntryCLM l m).comp (ContinuousLinearMap.apply ℝ (Fin n → Fin n → ℝ) v)).hasFDerivAt.comp
      y hG.hasFDerivAt).fderiv
  rw [hL]
  rfl

end Analysis
end DifferentialGeometry

end
