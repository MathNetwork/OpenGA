





import DifferentialGeometry.Tensor.Alternating.Bundle
import DifferentialGeometry.Tensor.Alternating.FDeriv
import DifferentialGeometry.Tensor.Alternating.Wedge
import DifferentialGeometry.Tensor.Exterior.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

noncomputable section

open Filter ContinuousAlternatingMap Set
open scoped Topology

variable {E F F' F'' G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup F''] [NormedSpace ℝ F'']
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {n m k : ℕ}

section RoughDifferentialForm

variable {n m k : ℕ}
variable {v : E}

variable (ω τ : E → E [⋀^Fin n]→L[ℝ] F)
variable (f : E → F)

@[simp]
theorem add_apply : (ω + τ) v = ω v + τ v :=
  rfl

@[simp]
theorem sub_apply : (ω - τ) v = ω v - τ v :=
  rfl

@[simp]
theorem neg_apply : (-ω) v = -ω v :=
  rfl

@[simp]
theorem smul_apply (ω : E → E [⋀^Fin n]→L[ℝ] F) (c : ℝ) : (c • ω) v = c • ω v :=
  rfl

@[simp]
theorem zero_apply : (0 : E → E [⋀^Fin n]→L[ℝ] F) v = 0 :=
  rfl

def ofSubsingleton :
    (E → E →L[ℝ] F) ≃ (E → E [⋀^Fin 1]→L[ℝ] F) where
  toFun f := fun e ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F 0 (f e)
  invFun f := fun e ↦ (ContinuousAlternatingMap.ofSubsingleton ℝ E F 0).symm (f e)
  left_inv _ := rfl
  right_inv _ := by simp

def constOfIsEmpty (x : F) : E → E [⋀^Fin 0]→L[ℝ] F :=
  fun _ ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) x

def ederiv (ω : E → E [⋀^Fin n]→L[ℝ] F) : E → E [⋀^Fin (n + 1)]→L[ℝ] F :=
  fun x ↦ .uncurryFin (fderiv ℝ ω x)

def ederivWithin (ω : E → E [⋀^Fin n]→L[ℝ] F) (s : Set E) : E → E [⋀^Fin (n + 1)]→L[ℝ] F :=
  fun (x : E) ↦ .uncurryFin (fderivWithin ℝ ω s x)

@[simp]
theorem ederivWithin_univ (ω : E → E [⋀^Fin n]→L[ℝ] F) :
    ederivWithin ω univ = ederiv ω := by
  ext1 x
  rw[ederivWithin, ederiv, fderivWithin_univ]

theorem ederivWithin_add (ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F) (s : Set E) {x : E} (hsx : UniqueDiffWithinAt ℝ s x)
    (hω₁ : DifferentiableWithinAt ℝ ω₁ s x) (hω₂ : DifferentiableWithinAt ℝ ω₂ s x) :
    ederivWithin (ω₁ + ω₂) s x = ederivWithin ω₁ s x + ederivWithin ω₂ s x := by
  simp [ederivWithin, fderivWithin_add hsx hω₁ hω₂, uncurryFin_add]

theorem ederivWithin_smul (ω : E → E [⋀^Fin n]→L[ℝ] F) (c : ℝ) (s : Set E) {x : E}
    (hsx : UniqueDiffWithinAt ℝ s x) (hω : DifferentiableWithinAt ℝ ω s x) :
      ederivWithin (c • ω) s x = c • ederivWithin ω s x := by
  simp [ederivWithin, fderivWithin_const_smul hsx hω, uncurryFin_smul]

theorem ederivWithin_constOfIsEmpty (s : Set E) (x : E) (y : F) :
    ederivWithin (constOfIsEmpty y) s x = .uncurryFin (fderivWithin ℝ (constOfIsEmpty y) s x) :=
  rfl

theorem Filter.EventuallyEq.ederivWithin_eq {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x) : ederivWithin ω₁ s x = ederivWithin ω₂ s x := by
  simp only[ederivWithin, uncurryFin, hs.fderivWithin_eq hx]

theorem Filter.EventuallyEq.ederivWithin_eq_of_mem {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : x ∈ s) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  hs.ederivWithin_eq (mem_of_mem_nhdsWithin hx hs :)

theorem Filter.EventuallyEq.ederivWithin_eq_of_insert {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[insert x s] x] ω₂) : ederivWithin ω₁ s x = ederivWithin ω₂ s x := by
  apply Filter.EventuallyEq.ederivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
  exact (mem_of_mem_nhdsWithin (mem_insert x s) hs :)

theorem Filter.EventuallyEq.ederivWithin' {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s t : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (ht : t ⊆ s) : ederivWithin ω₁ t =ᶠ[𝓝[s] x] ederivWithin ω₂ t :=
  (eventually_eventually_nhdsWithin.2 hs).mp <|
    eventually_mem_nhdsWithin.mono fun _y hys hs =>
      EventuallyEq.ederivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)

protected theorem Filter.EverntuallyEq.ederivWithin {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) : ederivWithin ω₁ s =ᶠ[𝓝[s] x] ederivWithin ω₂ s :=
  hs.ederivWithin' Subset.rfl

theorem Filter.EventuallyEq.ederivWithin_eq_nhds {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s : Set E} {x : E}
    (h : ω₁ =ᶠ[𝓝 x] ω₂) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  (h.filter_mono nhdsWithin_le_nhds).ederivWithin_eq h.self_of_nhds

theorem ederivWithin_congr {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s : Set E} {x : E}
    (hs : EqOn ω₁ ω₂ s) (hx : ω₁ x = ω₂ x) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).ederivWithin_eq hx

theorem ederivWithin_congr' {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s : Set E} {x : E}
    (hs : EqOn ω₁ ω₂ s) (hx : x ∈ s) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  ederivWithin_congr hs (hs hx)

theorem ederivWithin_apply (ω : E → E [⋀^Fin n]→L[ℝ] F) {s : Set E} {x : E}
    (h : DifferentiableWithinAt ℝ ω s x) (hs : UniqueDiffWithinAt ℝ s x) (v : Fin (n + 1) → E) :
      ederivWithin ω s x v = ∑ i, (-1) ^ i.val • fderivWithin ℝ (ω · (i.removeNth v)) s x (v i)
  := by
  simp only [ederivWithin, ContinuousAlternatingMap.uncurryFin_apply,
    ContinuousAlternatingMap.fderivWithin_apply h hs]

theorem ederivWithin_ederivWithin_apply (ω : E → E [⋀^Fin n]→L[ℝ] F) {s : Set E} {x}
    (hxx : x ∈ closure (interior s)) (hx : x ∈ s) (h : ContDiffWithinAt ℝ 2 ω s x)
    (hs : UniqueDiffOn ℝ s) :
    ederivWithin (ederivWithin ω s) s x = 0 := calc
  ederivWithin (ederivWithin ω s) s x =
    uncurryFin (fderivWithin ℝ (fun y ↦ uncurryFin (fderivWithin ℝ ω s y)) s x) := rfl
  _ = uncurryFin (uncurryFinCLM.comp <| fderivWithin ℝ (fderivWithin ℝ ω s) s x) := by
    congr 1
    let t :  Set (E →L[ℝ] E [⋀^Fin n]→L[ℝ] F) := univ
    let hst : MapsTo (fderivWithin ℝ ω s) s univ := by unfold MapsTo; intro x _; trivial
    have : DifferentiableWithinAt ℝ (fderivWithin ℝ ω s) s x := (h.fderivWithin_right
      (hs) (by ring_nf; exact le_of_eq rfl) (hx)).differentiableWithinAt
      (by simp only [ne_eq, one_ne_zero, not_false_eq_true])
    let ⟨ω'', h⟩ := this
    have uncurryDeriv := @ContinuousLinearMap.hasFDerivWithinAt ℝ _ _ _ _ _ _ _ _ _
      (@uncurryFinCLM ℝ E F _ _ _ _ _ n) (fderivWithin ℝ ω s x) t
    have chain : HasFDerivWithinAt (uncurryFinCLM ∘ (fderivWithin ℝ ω s)) (uncurryFinCLM ∘L ω'') s x
      := @HasFDerivWithinAt.comp ℝ _ _ _ _ _ _ _ _ _ _ (fderivWithin ℝ ω s) ω'' x s uncurryFinCLM
        uncurryFinCLM t uncurryDeriv h hst
    have := UniqueDiffOn.uniqueDiffWithinAt hs hx
    rw [h.fderivWithin this]
    exact chain.fderivWithin this
  _ = 0 :=
    uncurryFin_uncurryFinCLM_comp_of_symmetric <| h.isSymmSndFDerivWithinAt
      (by simp only [minSmoothness_of_isRCLikeNormedField, le_refl]) hs hxx hx

theorem ederivWithin_ederivWithin (ω : E → E [⋀^Fin n]→L[ℝ] F) {s : Set E} (h : ContDiffOn ℝ 2 ω s)
    (hs : UniqueDiffOn ℝ s) :
    EqOn (ederivWithin (ederivWithin ω s) s) 0 (s ∩ (closure (interior s))) :=
  fun _ ⟨ hx, hxx ⟩ => ederivWithin_ederivWithin_apply ω hxx hx (h.contDiffWithinAt hx) hs

theorem ederiv_add (ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F) {x : E} (hω₁ : DifferentiableAt ℝ ω₁ x)
    (hω₂ : DifferentiableAt ℝ ω₂ x) : ederiv (ω₁ + ω₂) x = ederiv ω₁ x + ederiv ω₂ x := by
  simp [ederiv, fderiv_add hω₁ hω₂, uncurryFin_add]

theorem ederiv_smul (ω : E → E [⋀^Fin n]→L[ℝ] F) (c : ℝ) {x : E} (hω : DifferentiableAt ℝ ω x) :
    ederiv (c • ω) x = c • ederiv ω x := by
  simp [ederiv, fderiv_const_smul hω, uncurryFin_smul]

theorem ederiv_constOfIsEmpty (x : E) (y : F) :
    ederiv (constOfIsEmpty y) x = .uncurryFin (fderiv ℝ (constOfIsEmpty y) x) :=
  rfl

theorem Filter.EventuallyEq.ederiv_eq {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {x : E}
    (h : ω₁ =ᶠ[𝓝 x] ω₂) : ederiv ω₁ x = ederiv ω₂ x := by
  ext v
  simp only [ederiv, ContinuousAlternatingMap.uncurryFin_apply, h.fderiv_eq]

protected theorem Filter.EventuallyEq.ederiv {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {x : E}
    (h : ω₁ =ᶠ[𝓝 x] ω₂) : ederiv ω₁ =ᶠ[𝓝 x] ederiv ω₂ :=
  h.eventuallyEq_nhds.mono fun _x hx ↦ hx.ederiv_eq

theorem ederiv_apply (ω : E → E [⋀^Fin n]→L[ℝ] F) {x : E} (hx : DifferentiableAt ℝ ω x) (v : Fin (n + 1) → E) :
    ederiv ω x v = ∑ i, (-1) ^ i.val • fderiv ℝ (ω · (i.removeNth v)) x (v i) := by
  simp only [ederiv, ContinuousAlternatingMap.uncurryFin_apply,
    ContinuousAlternatingMap.fderiv_apply hx]

theorem ederiv_ederiv_apply (ω : E → E [⋀^Fin n]→L[ℝ] F) {x : E} (h : ContDiffAt ℝ 2 ω x) :
  ederiv (ederiv ω) x = 0 := calc
  ederiv (ederiv ω) x = uncurryFin (fderiv ℝ (fun y ↦ uncurryFin (fderiv ℝ ω y)) x) := rfl
  _ = uncurryFin (uncurryFinCLM.comp <| fderiv ℝ (fderiv ℝ ω) x) := by
    congr 1
    have : DifferentiableAt ℝ (fderiv ℝ ω) x := (h.fderiv_right
      (by ring_nf; exact le_of_eq rfl)).differentiableAt
      (by simp only [ne_eq, one_ne_zero, not_false_eq_true])
    let ⟨ω'', h⟩ := this
    have uncurryDeriv := @ContinuousLinearMap.hasFDerivAt ℝ _ _ _ _ _ _ _ _ _
      (@uncurryFinCLM ℝ E F _ _ _ _ _ n) (fderiv ℝ ω x)
    have chain : HasFDerivAt (uncurryFinCLM ∘ (fderiv ℝ ω)) (uncurryFinCLM ∘L ω'') x
      := @HasFDerivAt.comp ℝ _ _ _ _ _ _ _ _ _ _ (fderiv ℝ ω) ω'' x uncurryFinCLM uncurryFinCLM
        uncurryDeriv h
    rw [h.fderiv]
    exact chain.fderiv
  _ = 0 :=
    uncurryFin_uncurryFinCLM_comp_of_symmetric <| h.isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField, le_refl])

theorem ederiv_ederiv (ω : E → E [⋀^Fin n]→L[ℝ] F) (h : ContDiff ℝ 2 ω) : ederiv (ederiv ω) = 0 :=
  funext fun _ ↦ ederiv_ederiv_apply ω h.contDiffAt

end RoughDifferentialForm

namespace RoughDifferentialForm

def domDomCongr (σ : Fin n ≃ Fin m) (ω : E → E [⋀^Fin n]→L[ℝ] F) : E → E [⋀^Fin m]→L[ℝ] F :=
  fun e => (ω e).domDomCongr σ

theorem domDomCongr_apply (σ : Fin n ≃ Fin m) (ω : E → E [⋀^Fin n]→L[ℝ] F) (e : E) (v : Fin m → E) :
    (domDomCongr σ ω) e v = (ω e) (v ∘ σ)  :=
  rfl

def pullback (f : E → F) (ω : F → F [⋀^Fin k]→L[ℝ] G) : E → E [⋀^Fin k]→L[ℝ] G :=
    fun x ↦ (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)

theorem pullback_zero (f : E → F) :
    pullback f (0 : F → F [⋀^Fin k]→L[ℝ] G) = 0 :=
  rfl

theorem pullback_add (f : E → F) (ω : F → F [⋀^Fin k]→L[ℝ] G) (τ : F → F [⋀^Fin k]→L[ℝ] G) :
    pullback f (ω + τ) = pullback f ω + pullback f τ :=
  rfl

theorem pullback_sub (f : E → F) (ω : F → F [⋀^Fin k]→L[ℝ] G) (τ : F → F [⋀^Fin k]→L[ℝ] G) :
    pullback f (ω - τ) = pullback f ω - pullback f τ :=
  rfl

theorem pullback_neg (f : E → F) (ω : F → F [⋀^Fin k]→L[ℝ] G) :
    - pullback f ω = pullback f (-ω) :=
  rfl

theorem pullback_smul (f : E → F) (ω : F → F [⋀^Fin k]→L[ℝ] G) (c : ℝ) :
    c • (pullback f ω) = pullback f (c • ω) :=
  rfl

theorem pullback_ofSubsingleton (f : E → F) (ω : F → F →L[ℝ] G) :
    pullback f (ofSubsingleton ω) = ofSubsingleton (fun e ↦ (ω (f e)).comp (fderiv ℝ f e)) :=
  rfl

theorem pullback_constOfIsEmpty (f : E → F) (g : G) :
    pullback f (constOfIsEmpty g) = fun _ ↦ (ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) g)
  := rfl

def iprod (ω : E → E [⋀^Fin (m + 1)]→L[ℝ] F) (v : E → E) : E → E [⋀^Fin m]→L[ℝ] F :=
    fun e => ContinuousAlternatingMap.curryFin (ω e) (v e)

theorem iprod_apply (ω : E → E [⋀^Fin (m + 1)]→L[ℝ] F) (v : E → E) (e : E) :
    iprod ω v e = ContinuousAlternatingMap.curryFin (ω e) (v e) :=
  rfl

theorem iprod_antisymm (ω : E → E [⋀^Fin (m + 2)]→L[ℝ] ℝ) (v w : E → E) (e : E) (m' : Fin m → E) :
    iprod (iprod ω v) w e m' = - iprod (iprod ω w) v e m' := by
  repeat
    rw[iprod_apply, curryFin_apply]
  let h := AlternatingMap.map_swap (ω e).toAlternatingMap (Fin.cons (w e) (Fin.cons (v e) m'))
    Fin.zero_ne_one
  rw [@coe_toAlternatingMap] at h
  rw [← h]
  clear h
  congr 1
  ext i
  obtain (rfl | ⟨ i , rfl ⟩) := i.eq_zero_or_eq_succ
  · simp
  obtain (rfl | ⟨ i , rfl ⟩) := i.eq_zero_or_eq_succ
  · simp
  · rw[Function.comp_apply, Equiv.swap_apply_of_ne_of_ne] <;>
    simp only [Fin.cons_succ, ← Fin.succ_zero_eq_one, ne_eq, Fin.succ_inj,
      Fin.succ_ne_zero, not_false_eq_true]

theorem iprod_iprod (ω : E → E [⋀^Fin (m + 2)]→L[ℝ] ℝ) (v : E → E) :
    iprod (iprod ω v) v = 0 := by
  ext e m'
  let h := iprod_antisymm ω v v e m'
  rw [eq_neg_iff_add_eq_zero, add_self_eq_zero] at h
  exact h

def wedge_product (ω₁ : E → E [⋀^Fin m]→L[ℝ] F) (ω₂ : E → E [⋀^Fin n]→L[ℝ] F') (f : F →L[ℝ] F' →L[ℝ] F'') :
    E → E [⋀^Fin (m + n)]→L[ℝ] F'' := fun e => ContinuousAlternatingMap.wedge_product (ω₁ e) (ω₂ e) f

notation ω₁ "∧r["f"]" ω₂ => wedge_product ω₁ ω₂ f
notation ω₁ "∧r" ω₂ => wedge_product ω₁ ω₂ (ContinuousLinearMap.mul ℝ ℝ)

theorem wedge_product_def {ω₁ : E → E [⋀^Fin m]→L[ℝ] F} {ω₂ : E → E [⋀^Fin n]→L[ℝ] F'} {f : F →L[ℝ] F' →L[ℝ] F''}
    {x : E} : (ω₁ ∧r[f] ω₂) x = ContinuousAlternatingMap.wedge_product (ω₁ x) (ω₂ x) f :=
  rfl

theorem wedge_product_mul {ω₁ : E → E [⋀^Fin m]→L[ℝ] ℝ} {ω₂ : E → E [⋀^Fin n]→L[ℝ] ℝ} {x : E} :
    (ω₁ ∧r ω₂) x =
    ContinuousAlternatingMap.wedge_product (ω₁ x) (ω₂ x) (ContinuousLinearMap.mul ℝ ℝ) :=
  rfl

theorem wedge_product_lsmul {ω₁ : E → E [⋀^Fin m]→L[ℝ] ℝ} {ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {x : E} :
    (ω₁ ∧r[ContinuousLinearMap.lsmul ℝ ℝ] ω₂) x =
    ContinuousAlternatingMap.wedge_product (ω₁ x) (ω₂ x) (ContinuousLinearMap.lsmul ℝ ℝ) :=
  rfl

theorem wedge_assoc [FiniteDimensional ℝ E]
    (ω₁ : E → E [⋀^Fin m]→L[ℝ] ℝ) (ω₂ : E → E [⋀^Fin n]→L[ℝ] ℝ) (ω₃ : E → E [⋀^Fin k]→L[ℝ] ℝ) :
    domDomCongr Fin.finAssoc.symm (ω₁ ∧r ω₂ ∧r ω₃) = (ω₁ ∧r ω₂) ∧r ω₃ := by
  ext x y
  rw[wedge_product_def, wedge_product_def, domDomCongr_apply, wedge_product_def, wedge_product_def,
    ← ContinuousAlternatingMap.domDomCongr_apply]
  exact ContinuousAlternatingMap.wedge_mul_assoc (ω₁ x) (ω₂ x) (ω₃ x) y

theorem add_wedge (ω₁ ω₂ : E → E [⋀^Fin m]→L[ℝ] F) (τ : E → E [⋀^Fin n]→L[ℝ] F') (f : F →L[ℝ] F' →L[ℝ] F'') :
    ((ω₁ + ω₂) ∧r[f] τ) = (ω₁ ∧r[f] τ) + (ω₂ ∧r[f] τ) := by
  ext1 x
  rw[wedge_product_def, _root_.add_apply, _root_.add_apply, wedge_product_def, wedge_product_def]
  exact ContinuousAlternatingMap.add_wedge (ω₁ x) (ω₂ x) (τ x) f

theorem wedge_add (ω : E → E [⋀^Fin m]→L[ℝ] F) (τ₁ τ₂ : E → E [⋀^Fin n]→L[ℝ] F') (f : F →L[ℝ] F' →L[ℝ] F'') :
    (ω ∧r[f] (τ₁ + τ₂)) = (ω ∧r[f] τ₁) + (ω ∧r[f] τ₂) := by
  ext1 x
  rw[wedge_product_def, _root_.add_apply, _root_.add_apply, wedge_product_def, wedge_product_def]
  exact ContinuousAlternatingMap.wedge_add (ω x) (τ₁ x) (τ₂ x) f

theorem smul_wedge (ω : E → E [⋀^Fin m]→L[ℝ] ℝ) (τ : E → E [⋀^Fin n]→L[ℝ] ℝ) (c : ℝ) :
    c • (ω ∧r τ) = (c • ω) ∧r τ := by
  ext1 x
  rw[_root_.smul_apply, wedge_product_mul, wedge_product_mul, _root_.smul_apply]
  exact (ContinuousAlternatingMap.smul_wedge c (ω x) (τ x)
    (ContinuousLinearMap.mul ℝ ℝ)).symm

theorem wedge_smul (ω : E → E [⋀^Fin m]→L[ℝ] ℝ) (τ : E → E [⋀^Fin n]→L[ℝ] ℝ) (c : ℝ) :
    c • (ω ∧r τ) = ω ∧r (c • τ) := by
  ext1 x
  rw[_root_.smul_apply, wedge_product_mul, wedge_product_mul, _root_.smul_apply]
  exact (ContinuousAlternatingMap.wedge_smul c (ω x) (τ x)
    (ContinuousLinearMap.mul ℝ ℝ)).symm

theorem wedge_antisymm [FiniteDimensional ℝ E]
    (ω : E → E [⋀^Fin m]→L[ℝ] ℝ) (τ : E → E [⋀^Fin n]→L[ℝ] ℝ) :
    (ω ∧r τ) = RoughDifferentialForm.domDomCongr Fin.finAddCongr ((-1 : ℝ)^(m*n) • (τ ∧r ω)) := by
  ext x y
  rw[wedge_product_mul, domDomCongr_apply, _root_.smul_apply,
    wedge_product_mul, ← ContinuousAlternatingMap.domDomCongr_apply]
  let h := ContinuousAlternatingMap.wedge_antisymm (ω x) (τ x)
  exact congrFun (congrArg DFunLike.coe h) y

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

theorem wedge_self_odd_zero [FiniteDimensional ℝ E]
    (ω : E → E [⋀^Fin m]→L[ℝ] ℝ) (m_odd : Odd m) :
    (ω ∧r ω) = 0 := by
  ext1 x
  rw[wedge_product_mul]
  exact ContinuousAlternatingMap.wedge_self_odd_zero (ω x) m_odd

theorem pullback_wedge (f : G → E) (ω₁ : E → E [⋀^Fin m]→L[ℝ] F) (ω₂ : E → E [⋀^Fin n]→L[ℝ] F')
    (f' : F →L[ℝ] F' →L[ℝ] F'') : pullback f (ω₁ ∧r[f'] ω₂) = pullback f ω₁ ∧r[f'] pullback f ω₂ := by
  ext x y
  rw[wedge_product_def, pullback, wedge_product_def, pullback, pullback,
    compContinuousLinearMap_apply]
  rw[ContinuousAlternatingMap.wedge_product_def, uncurryFinAdd,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply,
    ContinuousAlternatingMap.wedge_product_def, uncurryFinAdd,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  rw[uncurrySum.summand_mk]
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw[uncurrySum.summand_mk]
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    compContinuousLinearMap_apply, compContinuousLinearMap_apply]
  simp only [Function.comp_apply, smul_left_cancel_iff]
  rfl

theorem iprod_wedge [FiniteDimensional ℝ E]
    (ω : E → E [⋀^Fin (m + 1)]→L[ℝ] ℝ) (τ : E → E [⋀^Fin (n + 1)]→L[ℝ] ℝ)
    (v : E → E) :
      iprod (domDomCongr Fin.finAddFlipAssoc (ω ∧r τ)) v = ((iprod ω v) ∧r τ)
        + (-1 : ℝ)^(m + 1) • (domDomCongr Fin.finAddFlipAssoc (ω ∧r (iprod τ v))) := by
  funext e
  exact ContinuousAlternatingMap.iprod_wedge_product_mul (ω e) (τ e) (v e)

end RoughDifferentialForm
