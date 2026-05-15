import OpenGALib.Algebraic.BilinearForm.Basic
import OpenGALib.Riemannian.Metric.HasMetric

/-!
# Bridge from `RiemannianMetric.inner` to `BilinearForm.Form ℝ E`

Engineering plumbing connecting the metric's continuous bilinear form
`g.inner x : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ` to the
algebraic-core `BilinearForm.Form ℝ E`, so that
`OpenGALib.Algebraic.BilinearForm.Riesz` machinery applies on the Riesz
methods in `Metric/RiemannianMetric.lean`.

All declarations are **Eng** type-theoretic glue with no paper analogue,
hence `Util/` per OpenGA's anchor-purity discipline.
-/

open Bundle
open scoped ContDiff Manifold Topology Bundle

namespace Riemannian.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Eng.** Bridge from the metric's continuous bilinear form `g.inner x`
to the algebraic-core `BilinearForm.Form ℝ E`. -/
noncomputable def toBilinForm (g : RiemannianMetric I M) (x : M) :
    BilinearForm.Form ℝ E :=
  LinearMap.mk₂ ℝ
    (fun v w => g.inner x v w)
    (fun v₁ v₂ w => by
      simp only [show g.inner x (v₁ + v₂) = g.inner x v₁ + g.inner x v₂
        from (g.inner x).map_add v₁ v₂, ContinuousLinearMap.add_apply])
    (fun c v w => by
      simp only [show g.inner x (c • v) = c • g.inner x v
        from (g.inner x).map_smul c v, ContinuousLinearMap.smul_apply])
    (fun v w₁ w₂ => (g.inner x v).map_add w₁ w₂)
    (fun c v w => (g.inner x v).map_smul c w)

/-- **Eng.** Positive-definiteness of `toBilinForm`, transported from
`g.pos`. -/
theorem toBilinForm_isPosDef (g : RiemannianMetric I M) (x : M) :
    BilinearForm.IsPosDef (g.toBilinForm x) := by
  intro v hv
  show 0 < g.inner x v v
  exact g.pos x v hv

end Riemannian.RiemannianMetric
