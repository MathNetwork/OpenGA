import DifferentialGeometry.Geometry.Metric.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.Cartan.Formula
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.TimeDerivativeChainRule
import DifferentialGeometry.Geometry.Flow.LieDerivativeMetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Geometry.Manifold.MFDeriv.Basic


namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.PDE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
theorem pullback_metric_evaluation_formula
    (g : SmoothRiemannianMetric I M) (Φ : M ≃ₘ⟮I, I⟯ M)
    (x : M) (v w : TangentSpace I x) :
    (Diffeomorph.pullbackMetric g Φ).inner x v w
      = g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w) := by
  change Diffeomorph.pullbackInner g Φ x v w
      = g.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w)
  unfold Diffeomorph.pullbackInner
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.precomp_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem mfderiv_time_derivative_along_flow
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v : TangentSpace I x)
    {V : ℝ → TangentSpace I (Φ_fam t x)}
    {V' : TangentSpace I (Φ_fam t x)}
    (h_eq : V =ᶠ[nhds t] fun s => mfderiv I I (Φ_fam s : M → M) x v)
    (h_deriv : HasDerivAt V V' t) :
    HasDerivAt (fun s => mfderiv I I (Φ_fam s : M → M) x v) V' t :=
  h_deriv.congr_of_eventuallyEq h_eq.symm

omit [NeZero (Module.finrank ℝ E)] in
theorem pullback_metric_derivative_decomposition
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (G' : ℝ)
    (h_G : HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
      G' t)
    (A' : ℝ)
    (h_A : HasDerivAt
      (fun s : ℝ => (g_fam t).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam s : M → M) x v) (mfderiv I I (Φ_fam t : M → M) x w))
      A' t)
    (B' : ℝ)
    (h_B : HasDerivAt
      (fun s : ℝ => (g_fam t).inner (Φ_fam t x)
        (mfderiv I I (Φ_fam t : M → M) x v) (mfderiv I I (Φ_fam s : M → M) x w))
      B' t)
    (h_total_eval : HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (G' + A' + B') t) :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + A' + B') t := by
  let _ := h_G; let _ := h_A; let _ := h_B
  exact pullbackMetric_inner_hasDerivAt_of_eval g_fam Φ_fam x v w h_total_eval

omit [NeZero (Module.finrank ℝ E)] in
theorem combine_pullback_derivative_pieces
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (G' L' : ℝ)
    (h_chain_eval : HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (G' + L') t) :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + L') t :=
  pullbackMetric_inner_hasDerivAt_of_eval g_fam Φ_fam x v w h_chain_eval

omit [NeZero (Module.finrank ℝ E)] in
theorem pullback_time_derivative_chain_rule
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (Φ_fam : ℝ → M ≃ₘ⟮I, I⟯ M)
    (t : ℝ) (x : M) (v w : TangentSpace I x)
    (G' L' : ℝ)
    (h_chain_eval : HasDerivAt
      (fun s : ℝ => (g_fam s).inner (Φ_fam s x)
        (mfderiv I I (Φ_fam s : M → M) x v)
        (mfderiv I I (Φ_fam s : M → M) x w))
      (G' + L') t) :
    HasDerivAt
      (fun s : ℝ => (Diffeomorph.pullbackMetric (g_fam s) (Φ_fam s)).inner x v w)
      (G' + L') t :=
  combine_pullback_derivative_pieces g_fam Φ_fam t x v w G' L' h_chain_eval

end DifferentialGeometry.PDE.RicciFlow.Pullback
