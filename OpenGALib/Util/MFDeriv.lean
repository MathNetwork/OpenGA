import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Manifold-derivative extensions

Generic `mfderiv` lemmas that do not depend on any Riemannian / metric
structure. Self-contained signatures (no `variable` block) so each
theorem is fully reusable without typeclass-pollution from a shared
context.
-/

noncomputable section

open scoped Manifold

namespace Riemannian

/-- **Eng.** `mfderiv` distributes over `Finset.sum` (evaluated at a
tangent vector):
$$\mathrm{d}\Bigl(\sum_{i \in s} g_i\Bigr)(x)(v)
   \;=\; \sum_{i \in s} \mathrm{d}(g_i)(x)(v).$$
Wraps Mathlib's `HasMFDerivAt.sum`. -/
theorem mfderiv_finset_sum_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {ι : Type} (s : Finset ι) (g : ι → M → ℝ) (x : M) (v : TangentSpace I x)
    (hg : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ, ℝ) (g i) x) :
    (mfderiv I 𝓘(ℝ, ℝ) (fun y => ∑ i ∈ s, g i y) x v : ℝ)
      = ∑ i ∈ s, (mfderiv I 𝓘(ℝ, ℝ) (g i) x v : ℝ) := by
  classical
  have h : HasMFDerivAt I 𝓘(ℝ, ℝ) (∑ i ∈ s, g i) x
      (∑ i ∈ s, mfderiv I 𝓘(ℝ, ℝ) (g i) x) :=
    HasMFDerivAt.sum (fun i hi => (hg i hi).hasMFDerivAt)
  have h' : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => ∑ i ∈ s, g i y) x
      (∑ i ∈ s, mfderiv I 𝓘(ℝ, ℝ) (g i) x) := by
    convert h using 1
    funext y
    exact (Finset.sum_apply y s g).symm
  rw [h'.mfderiv]
  exact ContinuousLinearMap.sum_apply s _ v

end Riemannian

end
