


import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs

section LinearIsometry

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
    [Module.Finite 𝕜 F]

theorem LinearIsometry.comp_contDiff_iff {L : E →ₗᵢ[𝕜] F} {f : G → E} {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (L ∘ f) ↔ ContDiff 𝕜 n f := by
  have hL : LinearMap.ker L.toLinearMap = ⊥ := LinearMap.ker_eq_bot_of_injective L.injective
  have ⟨K', hK'⟩ := LinearMap.exists_leftInverse_of_injective L.toLinearMap hL
  let K : F →L[𝕜] E := LinearMap.toContinuousLinearMap K'
  constructor
  · intro h
    have h2 : ContDiff 𝕜 n (K ∘ (L ∘ f)) := ContDiff.comp K.contDiff h
    have e1 : K ∘ L ∘ f = f := by
      ext x
      exact LinearMap.ext_iff.1 hK' (f x)
    rwa [e1] at h2
  · intro h
    exact ContDiff.comp L.contDiff h

end LinearIsometry
