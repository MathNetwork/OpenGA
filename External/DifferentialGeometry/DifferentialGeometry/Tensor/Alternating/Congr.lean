


import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.Basic

noncomputable section

namespace ContinuousAlternatingMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {ι ι' : Type*}

def domDomCongr (σ : ι ≃ ι') (f : M [⋀^ι]→L[𝕜] N) : M [⋀^ι']→L[𝕜] N :=
  { f.toContinuousMultilinearMap.domDomCongr σ with
    toFun := fun v => f (v ∘ σ)
    map_eq_zero_of_eq' := fun v i j hv hij =>
      f.map_eq_zero_of_eq (v ∘ σ) (i := σ.symm i) (j := σ.symm j)
        (by simpa using hv) (σ.symm.injective.ne hij) }

@[simp]
theorem domDomCongr_apply (σ : ι ≃ ι') (f : M [⋀^ι]→L[𝕜] N) (v : ι' → M) :
    (domDomCongr σ f) v = f (v ∘ σ) :=
  rfl

@[simp]
theorem domDomCongr_refl (f : M [⋀^ι]→L[𝕜] N) :
    domDomCongr (Equiv.refl ι) f = f :=
  rfl

variable {m n : ℕ}

theorem domDomCongr_add (e : Fin m ≃ Fin n)
    (f g : M [⋀^Fin m]→L[𝕜] N) :
    domDomCongr e (f + g) = domDomCongr e f + domDomCongr e g := by
  ext x; simp [domDomCongr_apply, add_apply]

theorem domDomCongr_sum {ι : Type*}
    (e : Fin m ≃ Fin n) (s : Finset ι) (f : ι → M [⋀^Fin m]→L[𝕜] N) :
    domDomCongr e (∑ i ∈ s, f i) = ∑ i ∈ s, domDomCongr e (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext; simp [domDomCongr_apply]
  | insert _ _ hni ih =>
    rw [Finset.sum_insert hni, domDomCongr_add, ih, Finset.sum_insert hni]

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

theorem alternatization_domDomCongr
    (e : ι₁ ≃ ι₂) (T : MultilinearMap 𝕜 (fun _ : ι₁ => M) N) :
    MultilinearMap.alternatization (T.domDomCongr e) =
      (MultilinearMap.alternatization T).domDomCongr e := by
  ext v; simp only [MultilinearMap.alternatization_apply, AlternatingMap.domDomCongr_apply,
    MultilinearMap.domDomCongr_apply]
  rw [← Equiv.sum_comp (Equiv.permCongr e)]; congr 1; ext σ
  simp only [Equiv.Perm.sign_permCongr, Function.comp]
  congr 2; funext i; simp [Equiv.permCongr_apply]

end ContinuousAlternatingMap
