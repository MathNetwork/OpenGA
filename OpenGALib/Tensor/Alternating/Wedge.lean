import OpenGALib.Algebraic.Auxiliary.Perm
import OpenGALib.Algebraic.Auxiliary.MultiKroneckerDelta
import OpenGALib.Algebraic.Auxiliary.Basis
import OpenGALib.Algebraic.Auxiliary.ShuffleSplit
import OpenGALib.Tensor.Alternating.Congr
import OpenGALib.Tensor.Alternating.Comp
import OpenGALib.Tensor.Alternating.Curry
import OpenGALib.Tensor.Product.Defs
import OpenGALib.Tensor.Alternating.Basis

/-
d(Sum_J ω_J dx^J) := Sum dω_J ∧ dx^J
-/

/-!
# Wedge product of continuous alternating maps

The wedge product `α ∧ β`, its bilinear / sign / associativity / Leibniz
properties, and the elementary-covector basis expansion.
-/

noncomputable section

namespace ContinuousAlternatingMap

section wedge

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {M'' : Type*} [NormedAddCommGroup M''] [NormedSpace 𝕜 M'']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {N' : Type*} [NormedAddCommGroup N'] [NormedSpace 𝕜 N']
  {N'' : Type*} [NormedAddCommGroup N''] [NormedSpace 𝕜 N'']
  {m n p m' d : ℕ}

/-- The wedge product of two continuous alternating maps `g` an `h` with respect to a
bilinear map `f`. -/
def wedge_product (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') : M [⋀^Fin (m + n)]→L[𝕜] N'' :=
  uncurryFinAdd (f.compContinuousAlternatingMap₂ g h)

-- TODO: change notation
notation g "∧["f"]" h => wedge_product g h f
notation g "∧["𝕜"]" h => wedge_product g h (ContinuousLinearMap.mul 𝕜 𝕜)

/-- Wedge of a continuous linear functional (1-cotangent) with an alternating
`n`-form, producing an alternating `(n + 1)`-form. The 1-cotangent `α : M →L[𝕜] 𝕜`
is viewed as an alternating 1-form via `ofSubsingleton`; the result is reindexed
from `Fin (1 + n)` to `Fin (n + 1)` via `finAddFlip`. -/
noncomputable def covectorWedge (α : M →L[𝕜] 𝕜) (β : M [⋀^Fin n]→L[𝕜] 𝕜) :
    M [⋀^Fin (n + 1)]→L[𝕜] 𝕜 :=
  domDomCongr finAddFlip
    (wedge_product (ofSubsingleton 𝕜 M 𝕜 0 α) β (ContinuousLinearMap.mul 𝕜 𝕜))

@[inherit_doc]
notation:70 α " ∧₁ " β => covectorWedge α β

theorem wedge_product_def {g : M [⋀^Fin m]→L[𝕜] N} {h : M [⋀^Fin n]→L[𝕜] N'}
    {f : N →L[𝕜] N' →L[𝕜] N''} {x : Fin (m + n) → M} :
    (g ∧[f] h) x = uncurryFinAdd (f.compContinuousAlternatingMap₂ g h) x :=
  rfl

open scoped TensorProduct

/-- The wedge product satisfies `m! * n! • (g ∧ h) v = Alt(g ⊗_f h) v`, proved via
`domCoprod_alternization_eq` from Mathlib. -/
theorem factorial_nsmul_wedge_product_eq_alternatization
    (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (v : Fin (m + n) → M) :
    (m.factorial * n.factorial) • (g ∧[f] h) v =
      MultilinearMap.alternatization (tensorProductMap g h f).toMultilinearMap v := by
  -- Factor tensorProductMap.toMM through domCoprod + TensorProduct.lift
  let φ : N ⊗[𝕜] N' →ₗ[𝕜] N'' := TensorProduct.lift
    { toFun := fun n => (f n).toLinearMap
      map_add' := by intro x y; ext; simp [map_add]
      map_smul' := by intro c x; ext; simp [map_smul] }
  have hφ : ∀ a b, φ (a ⊗ₜ[𝕜] b) = f a b := fun _ _ => rfl
  have h_factor : (tensorProductMap g h f).toMultilinearMap =
      (φ.compMultilinearMap (MultilinearMap.domCoprod
        ↑g.toAlternatingMap ↑h.toAlternatingMap)).domDomCongr finSumFinEquiv := by
    ext x; simp [tensorProductMap, MultilinearMap.domDomCongr_apply,
      LinearMap.compMultilinearMap_apply, MultilinearMap.domCoprod_apply, hφ]; rfl
  rw [h_factor, ContinuousAlternatingMap.alternatization_domDomCongr,
    LinearMap.compMultilinearMap_alternatization,
    MultilinearMap.domCoprod_alternization_eq, Fintype.card_fin, Fintype.card_fin]
  simp only [AlternatingMap.domDomCongr_apply, LinearMap.compAlternatingMap_apply,
    AlternatingMap.smul_apply, map_nsmul]
  change _ = _ • φ ((g.toAlternatingMap.domCoprod h.toAlternatingMap) (v ∘ ⇑finSumFinEquiv))
  rw [show φ ((g.toAlternatingMap.domCoprod h.toAlternatingMap) (v ∘ ⇑finSumFinEquiv)) =
    (uncurrySum (f.compContinuousAlternatingMap₂ g h)) (v ∘ ⇑finSumFinEquiv) from
    congr_fun (congr_arg DFunLike.coe
      (lift_comp_domCoprod_eq_uncurrySum g h f φ hφ)) _]; rfl

/-- The wedge product agrees with the standard definition:
`g ∧ h = 1/(m! * n!) • Alt(g ⊗_f h)` where `Alt` is `MultilinearMap.alternatization`. -/
theorem wedge_product_eq_alternatization [CharZero 𝕜]
    (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') (v : Fin (m + n) → M) :
    (g ∧[f] h) v = ((↑(m.factorial * n.factorial) : 𝕜))⁻¹ •
      MultilinearMap.alternatization (tensorProductMap g h f).toMultilinearMap v := by
  have h_ne : (↑(m.factorial * n.factorial) : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.mul_pos (Nat.factorial_pos m) (Nat.factorial_pos n)).ne'
  have h_eq := factorial_nsmul_wedge_product_eq_alternatization g h f v
  rw [← h_eq, ← Nat.cast_smul_eq_nsmul 𝕜, inv_smul_smul₀ h_ne]

/- It suffices to prove that ((elementaryCovector b I) ∧[𝕜] (elementaryCovector b J)) agrees with (elementaryCovector b (Fin.addCases I J) on any basis for (Fin k \to E). So it suffices to prove that they agree on (B (p 1), …, B(p (k+l))) for any p : Fin (k + l) \to n, where n = dim E and B is the basis for E dual to E*. We split this into the following cases:

1. If p is not injective, then both sides are zero since ((elementaryCovector b I) ∧[𝕜] (elementaryCovector b J)) and (elementaryCovector b (Fin.addCases I J) are alternating.
2. If p contains an index that does not appear in either I or J, then both sides are zero by elementaryCovector_basis_eval_eq_zero in Basis.lean
3. If p = Fin.addCases I J and p is injective, then we can compute via wedge_product_eq_alternatization that:

`((elementaryCovector b I) ∧[𝕜] (elementaryCovector b J)) (B ∘ p) = 1/(k! l!) * Alt((elementaryCovector b I) ⨂ (elementaryCovector b J)) (B ∘ p)`
` = 1/(k! l!) SUM_{σ ∈ S_(k+l)} (sign σ) * ((elementaryCovector b I) (B ∘ p ∘ σ(1), ..., B ∘ p ∘ σ(k))) * ((elementaryCovector b I) (B ∘ p ∘ σ(k+1), ..., B ∘ p ∘ σ(k+l)))`

Since p = IJ is injective, by elementaryCovector_basis_eval_eq_zero the only terms in this sum that give nonzero values are the cases when σ permutes the first k indices and the last l indices of p seperately. That is, when σ = τμ with τ ∈ S_k and μ ∈ S_l, so that sign (σ) = sign(τ) * sign (μ)
Therefore

`((elementaryCovector b I) ∧[𝕜] (elementaryCovector b J)) (B ∘ p) = 1/(k! l!) SUM_{τ ∈ S_k, μ ∈ S_l} (sign τ) * (sign μ) * ((elementaryCovector b I) (B ∘ p ∘ τ)) * ((elementaryCovector b J) (B ∘ p ∘ μ))`
` = (1/k! SUM_{τ ∈ S_k} (sign τ) * ((elementaryCovector b I) (B ∘ p ∘ τ))) * (1/l! SUM_{μ ∈ S_l} (sign μ) * ((elementaryCovector b I) (B ∘ p ∘ μ)))`
` = Alt(elementaryCovector b I) (B ∘ p(1), ..., B ∘ p(k)) * Alt(elementaryCovector b J) (B ∘ p(k+1), ..., B ∘ p(k+l))`
` = (elementaryCovector b I) (B ∘ p(1), ..., B ∘ p(k)) * (elementaryCovector b J) (B ∘ p(k+1), ..., B ∘ p(k+l))`
` = 1 = (elementaryCovector b (Fin.addCases I J)) (B ∘ p)`

4. If p = (Fin.addCases) ∘ σ for some permutation σ and is injective, then this reduces to case 3. Sice the effect of σ is merely to multiply both sides of the calculation by sign σ.
-/
theorem elementaryCovector_wedge [FiniteDimensional 𝕜 M] [CompleteSpace 𝕜] [CharZero 𝕜]
    (b : Module.Basis (Fin d) 𝕜 (M →L[𝕜] 𝕜))
    (I : Fin m' → Fin d) (J : Fin p → Fin d) :
    ((elementaryCovector b I) ∧[𝕜] (elementaryCovector b J)) =
      (elementaryCovector b (Fin.addCases I J) :
        M [⋀^Fin (m' + p)]→L[𝕜] 𝕜) := by
  -- Step 1: Construct the predual basis B of E with b i (B j) = δ_{ij}
  obtain ⟨B, dual⟩ := exists_predual_basis b
  -- Step 2: Reduce to checking on basis vectors via ext_alternating.
  -- It suffices to show both sides agree on (B (v 0), ..., B (v (m'+p-1)))
  -- for every injective v : Fin (m' + p) → Fin d.
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply B.ext_alternating
  intro v hv
  -- v : Fin (m' + p) → Fin d is injective
  -- Goal: (eI ∧ eJ) (B ∘ v) = e_{IJ} (B ∘ v)
  change ((elementaryCovector b I) ∧[𝕜] (elementaryCovector b J)) (B ∘ v) =
    elementaryCovector b (Fin.addCases I J) (B ∘ v)
  -- Step 3: Evaluate RHS via elementaryCovector_basis_eval
  rw [elementaryCovector_basis_eval B b dual (Fin.addCases I J) v]
  -- Step 4: Expand LHS via wedge_product_eq_alternatization
  have lhs_eq := wedge_product_eq_alternatization (elementaryCovector b I)
    (elementaryCovector b J) (ContinuousLinearMap.mul 𝕜 𝕜) (⇑B ∘ v)
  rw [lhs_eq, MultilinearMap.alternatization_apply]
  -- Step 5: Simplify the alternatization sum
  simp_rw [MultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.coe_coe,
    tensorProductMap_apply, ContinuousLinearMap.mul_apply']
  -- Step 6: Normalize compositions and rewrite elementaryCovector to multiKroneckerDelta
  simp_rw [show ∀ (σ : Equiv.Perm (Fin (m' + p))),
    (fun i => (⇑B ∘ v) (σ i)) ∘ Fin.castAdd p = ⇑B ∘ (v ∘ σ ∘ Fin.castAdd p) from fun _ => rfl,
    show ∀ (σ : Equiv.Perm (Fin (m' + p))),
    (fun i => (⇑B ∘ v) (σ i)) ∘ Fin.natAdd m' = ⇑B ∘ (v ∘ σ ∘ Fin.natAdd m') from fun _ => rfl,
    elementaryCovector_basis_eval B b dual]
  -- Step 7: Apply the Cauchy-Binet identity for multiKroneckerDelta
  exact Fin.multiKroneckerDelta_cauchyBinet I J v

/- The wedge product wrt multiplication -/
theorem wedge_product_mul {g : M [⋀^Fin m]→L[𝕜] 𝕜} {h : M [⋀^Fin n]→L[𝕜] 𝕜} {x : Fin (m + n) → M} :
    (g ∧[ContinuousLinearMap.mul 𝕜 𝕜] h) x =
    uncurryFinAdd ((ContinuousLinearMap.mul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) x :=
  rfl

/- The wedge product wrt scalar multiplication -/
theorem wedge_product_lsmul {g : M [⋀^Fin m]→L[𝕜] 𝕜} {h : M [⋀^Fin n]→L[𝕜] N}
    {x : Fin (m + n) → M} :
      (g ∧[ContinuousLinearMap.lsmul 𝕜 𝕜] h) x =
      uncurryFinAdd ((ContinuousLinearMap.lsmul 𝕜 𝕜).compContinuousAlternatingMap₂ g h) x :=
  rfl

/- Left distributivity of wedge product -/
theorem add_wedge (g₁ g₂ : M [⋀^Fin m]→L[𝕜] N)
    (h : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
      ((g₁ + g₂) ∧[f] h) = (g₁ ∧[f] h) + (g₂ ∧[f] h) := by
  ext x
  rw[add_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  repeat
    rw[uncurrySum.summand_mk]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
      Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
      ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
      ContinuousMultilinearMap.flipAlternating_apply,
      ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw[← smul_add, add_apply, map_add, ContinuousLinearMap.add_apply, smul_add]

/- Right distributivity of wedge product -/
theorem wedge_add (g : M [⋀^Fin m]→L[𝕜] N)
    (h₁ h₂ : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
      (g ∧[f] (h₁ + h₂)) = (g ∧[f] h₁) + (g ∧[f] h₂) := by
  ext x
  rw[add_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.sum_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  repeat
    rw[uncurrySum.summand_mk]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
      Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
      ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
      ContinuousMultilinearMap.flipAlternating_apply,
      ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw[add_apply, map_add, smul_add]

/-- Left scalar-linearity of the wedge product. -/
theorem smul_wedge (c : 𝕜) (g : M [⋀^Fin m]→L[𝕜] N)
    (h : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
      ((c • g) ∧[f] h) = c • (g ∧[f] h) := by
  ext x
  rw [smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  repeat
    rw [uncurrySum.summand_mk]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
      Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
      ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
      ContinuousMultilinearMap.flipAlternating_apply,
      ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw [ContinuousAlternatingMap.smul_apply, f.map_smul, ContinuousLinearMap.smul_apply, smul_comm]

/-- Right scalar-linearity of the wedge product. -/
theorem wedge_smul (c : 𝕜) (g : M [⋀^Fin m]→L[𝕜] N)
    (h : M [⋀^Fin n]→L[𝕜] N') (f : N →L[𝕜] N' →L[𝕜] N'') :
      (g ∧[f] (c • h)) = c • (g ∧[f] h) := by
  ext x
  rw [smul_apply, wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    wedge_product_def, uncurryFinAdd, domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  repeat
    rw [uncurrySum.summand_mk]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
      Function.comp_apply, ContinuousMultilinearMap.uncurrySum_apply,
      ContinuousMultilinearMap.flipMultilinear_apply, coe_toContinuousMultilinearMap,
      ContinuousMultilinearMap.flipAlternating_apply,
      ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw [ContinuousAlternatingMap.smul_apply, ContinuousLinearMap.map_smul, smul_comm]

/-- Operator norm bound for the wedge product:
`‖g ∧[f] h‖ ≤ #(ModSumCongr (Fin m) (Fin n)) · ‖f‖ · ‖g‖ · ‖h‖`.
The constant is the number of `(m,n)`-shuffles, equal to `(m+n).choose m`. -/
theorem norm_wedge_product_le (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N')
    (f : N →L[𝕜] N' →L[𝕜] N'') :
    ‖g ∧[f] h‖ ≤
      Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) * (‖f‖ * ‖g‖ * ‖h‖) := by
  refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_
  change ‖uncurryFinAdd (f.compContinuousAlternatingMap₂ g h) v‖ ≤ _
  rw [uncurryFinAdd, ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply,
      ContinuousMultilinearMap.sum_apply]
  have key : ∀ q : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
      ‖uncurrySum.summand (f.compContinuousAlternatingMap₂ g h) q
          (v ∘ ⇑finSumFinEquiv)‖ ≤ (‖f‖ * ‖g‖ * ‖h‖) * ∏ i, ‖v i‖ := by
    intro q
    induction q using Quotient.inductionOn' with | h σ =>
    rw [uncurrySum_summand_eval]
    have hsign : ∀ z : N'', ‖(Equiv.Perm.sign σ : ℤˣ) • z‖ = ‖z‖ := fun z => by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
    rw [hsign]
    change ‖f (g (fun i => (v ∘ ⇑finSumFinEquiv) (σ (Sum.inl i))))
            (h (fun i => (v ∘ ⇑finSumFinEquiv) (σ (Sum.inr i))))‖ ≤ _
    calc ‖f (g _) (h _)‖
        ≤ ‖f‖ * ‖g (fun i => (v ∘ ⇑finSumFinEquiv) (σ (Sum.inl i)))‖ *
            ‖h (fun i => (v ∘ ⇑finSumFinEquiv) (σ (Sum.inr i)))‖ := f.le_opNorm₂ _ _
      _ ≤ ‖f‖ * (‖g‖ * ∏ i, ‖(v ∘ ⇑finSumFinEquiv) (σ (Sum.inl i))‖) *
            (‖h‖ * ∏ i, ‖(v ∘ ⇑finSumFinEquiv) (σ (Sum.inr i))‖) := by
          gcongr
          · exact g.le_opNorm _
          · exact h.le_opNorm _
      _ = ‖f‖ * ‖g‖ * ‖h‖ *
            ((∏ i, ‖(v ∘ ⇑finSumFinEquiv) (σ (Sum.inl i))‖) *
              ∏ i, ‖(v ∘ ⇑finSumFinEquiv) (σ (Sum.inr i))‖) := by ring
      _ = ‖f‖ * ‖g‖ * ‖h‖ * ∏ k : Fin m ⊕ Fin n, ‖(v ∘ ⇑finSumFinEquiv) (σ k)‖ := by
          rw [← Fintype.prod_sum_type (fun k => ‖(v ∘ ⇑finSumFinEquiv) (σ k)‖)]
      _ = ‖f‖ * ‖g‖ * ‖h‖ * ∏ k : Fin m ⊕ Fin n, ‖(v ∘ ⇑finSumFinEquiv) k‖ := by
          rw [Equiv.prod_comp σ (fun k => ‖(v ∘ ⇑finSumFinEquiv) k‖)]
      _ = ‖f‖ * ‖g‖ * ‖h‖ * ∏ i, ‖v i‖ := by
          simp only [Function.comp_apply]
          rw [Equiv.prod_comp finSumFinEquiv (fun i => ‖v i‖)]
  calc ‖∑ q, uncurrySum.summand (f.compContinuousAlternatingMap₂ g h) q
            (v ∘ ⇑finSumFinEquiv)‖
      ≤ ∑ q, ‖uncurrySum.summand (f.compContinuousAlternatingMap₂ g h) q
            (v ∘ ⇑finSumFinEquiv)‖ := norm_sum_le _ _
    _ ≤ ∑ _q : Equiv.Perm.ModSumCongr (Fin m) (Fin n),
          (‖f‖ * ‖g‖ * ‖h‖) * ∏ i, ‖v i‖ := Finset.sum_le_sum fun q _ => key q
    _ = (Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) : ℝ) *
          ((‖f‖ * ‖g‖ * ‖h‖) * ∏ i, ‖v i‖) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) * (‖f‖ * ‖g‖ * ‖h‖) *
          ∏ i, ‖v i‖ := by ring

/-- The wedge product as a continuous bilinear map. -/
noncomputable def wedge_productL (f : N →L[𝕜] N' →L[𝕜] N'') :
    (M [⋀^Fin m]→L[𝕜] N) →L[𝕜] (M [⋀^Fin n]→L[𝕜] N') →L[𝕜]
        (M [⋀^Fin (m + n)]→L[𝕜] N'') :=
  LinearMap.mkContinuous₂
    { toFun := fun g =>
        { toFun := fun h => wedge_product g h f
          map_add' := fun h₁ h₂ => wedge_add g h₁ h₂ f
          map_smul' := fun c h => wedge_smul c g h f }
      map_add' := fun g₁ g₂ => by ext h : 1; exact add_wedge g₁ g₂ h f
      map_smul' := fun c g => by ext h : 1; exact smul_wedge c g h f }
    (Fintype.card (Equiv.Perm.ModSumCongr (Fin m) (Fin n)) * ‖f‖ + 1) fun g h => by
      change ‖wedge_product g h f‖ ≤ _
      have hwedge := norm_wedge_product_le g h f
      nlinarith [hwedge, norm_nonneg g, norm_nonneg h, norm_nonneg f]

@[simp] theorem wedge_productL_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^Fin m]→L[𝕜] N) (h : M [⋀^Fin n]→L[𝕜] N') :
    wedge_productL f g h = wedge_product g h f := rfl

/-- LHS evaluation formula: `uncurryFin` of a `precompL` of `wedge_productL` expands to
a sum over derivative positions, with each summand being a wedge product. -/
theorem uncurryFin_wedge_productL_precompL_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (v : Fin (m + n + 1) → M) :
    uncurryFin ((wedge_productL f).precompL M g' h) v =
      ∑ k : Fin (m + n + 1), (-1 : ℤ) ^ k.val •
        wedge_product (g' (v k)) h f (k.removeNth v) := by
  rw [uncurryFin_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [ContinuousLinearMap.precompL_apply, wedge_productL_apply]

/-- RHS evaluation formula: the wedge product of `uncurryFin g'` with `h`, evaluated at
`v ∘ finAddFlipAssoc`, pushes `uncurryFin` through the bilinear `f` to give a sum over
derivative positions within each shuffle summand. -/
theorem wedge_product_uncurryFin_apply (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N')
    (v : Fin (m + n + 1) → M) :
    domDomCongr Fin.finAddFlipAssoc (wedge_product (uncurryFin g') h f) v =
      (wedge_product (uncurryFin g') h f) (v ∘ ⇑Fin.finAddFlipAssoc) := by
  rw [ContinuousAlternatingMap.domDomCongr_apply]

/-- Antisymmetrizing a left-precomposition of `wedge_productL` equals wedging the
antisymmetrization on the left. The `Fin.finAddFlipAssoc` rewrites
`Fin (m + 1 + n)` to `Fin (m + n + 1)`.

Both sides are the alternation of the same underlying multilinear map
`v ↦ f (g' (v 0) (v 1, …, v m)) (h (v_{m+1}, …, v_{m+n}))`: the LHS computes it by
alternating the derivative slot (via `uncurryFin`) then the wedge slots (via
`uncurrySum`), the RHS by first alternating the derivative slot into the left factor
(via `uncurryFin g'`) then wedging the result with `h`. -/
theorem uncurryFin_wedge_productL_precompL (f : N →L[𝕜] N' →L[𝕜] N'')
    (g' : M →L[𝕜] (M [⋀^Fin m]→L[𝕜] N)) (h : M [⋀^Fin n]→L[𝕜] N') :
    uncurryFin ((wedge_productL f).precompL M g' h) =
      domDomCongr Fin.finAddFlipAssoc
        (wedge_product (uncurryFin g') h f) := by
  ext v
  rw [uncurryFin_wedge_productL_precompL_apply, wedge_product_uncurryFin_apply]
  -- LHS = ∑ k, (-1)^k • wedge_product (g' (v k)) h f (k.removeNth v)
  -- RHS = (wedge_product (uncurryFin g') h f) (v ∘ finAddFlipAssoc)
  -- Both sides compute the full alternation of `w ↦ f(g'(w₀)(w₁,…,wₘ))(h(wₘ₊₁,…,wₘ₊ₙ))`.
  -- The LHS sums over `(k, σ)` derivative-position × (m,n)-shuffle pairs.
  -- The RHS sums over `(τ, i)` (m+1,n)-shuffle × left-block-position pairs.
  -- These are matched by `derivShuffleEquivLeft`.
  sorry

/-- Antisymmetrizing a right-precomposition of `wedge_productL` equals wedging the
antisymmetrization on the right, with a sign `(-1)^m` from moving the new differentiation
index past the `m` left-factor indices. -/
theorem uncurryFin_wedge_productL_precompR (f : N →L[𝕜] N' →L[𝕜] N'')
    (g : M [⋀^Fin m]→L[𝕜] N) (h' : M →L[𝕜] (M [⋀^Fin n]→L[𝕜] N')) :
    uncurryFin ((wedge_productL f).precompR M g h') =
      ((-1 : 𝕜) ^ m) • wedge_product g (uncurryFin h') f := by
  sorry

private theorem zero_wedge' (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    wedge_product (0 : M [⋀^Fin m]→L[𝕜] 𝕜) h (ContinuousLinearMap.mul 𝕜 𝕜) = 0 := by
  have := add_wedge (0 : M [⋀^Fin m]→L[𝕜] 𝕜) 0 h (ContinuousLinearMap.mul 𝕜 𝕜)
  simp at this; exact this

private theorem wedge_zero' (g : M [⋀^Fin m]→L[𝕜] 𝕜) :
    wedge_product g (0 : M [⋀^Fin n]→L[𝕜] 𝕜) (ContinuousLinearMap.mul 𝕜 𝕜) = 0 := by
  have := wedge_add g (0 : M [⋀^Fin n]→L[𝕜] 𝕜) 0 (ContinuousLinearMap.mul 𝕜 𝕜)
  simp at this; exact this

private theorem sum_wedge_left {ι : Type*} (s : Finset ι)
    (g : ι → M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    wedge_product (∑ i ∈ s, g i) h (ContinuousLinearMap.mul 𝕜 𝕜) =
    ∑ i ∈ s, wedge_product (g i) h (ContinuousLinearMap.mul 𝕜 𝕜) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_wedge']
  | insert _ _ hni ih =>
    rw [Finset.sum_insert hni, add_wedge, ih, Finset.sum_insert hni]

private theorem sum_wedge_right {ι : Type*} (s : Finset ι)
    (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : ι → M [⋀^Fin n]→L[𝕜] 𝕜) :
    wedge_product g (∑ i ∈ s, h i) (ContinuousLinearMap.mul 𝕜 𝕜) =
    ∑ i ∈ s, wedge_product g (h i) (ContinuousLinearMap.mul 𝕜 𝕜) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wedge_zero']
  | insert _ _ hni ih =>
    rw [Finset.sum_insert hni, wedge_add, ih, Finset.sum_insert hni]

private theorem sum_smul_wedge_left {ι : Type*} (s : Finset ι)
    (c : ι → 𝕜) (g : ι → M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    wedge_product (∑ i ∈ s, c i • g i) h (ContinuousLinearMap.mul 𝕜 𝕜) =
    ∑ i ∈ s, c i • wedge_product (g i) h (ContinuousLinearMap.mul 𝕜 𝕜) := by
  rw [sum_wedge_left]; congr 1; ext i; rw [← smul_wedge]

private theorem sum_smul_wedge_right {ι : Type*} (s : Finset ι)
    (g : M [⋀^Fin m]→L[𝕜] 𝕜) (c : ι → 𝕜) (h : ι → M [⋀^Fin n]→L[𝕜] 𝕜) :
    wedge_product g (∑ i ∈ s, c i • h i) (ContinuousLinearMap.mul 𝕜 𝕜) =
    ∑ i ∈ s, c i • wedge_product g (h i) (ContinuousLinearMap.mul 𝕜 𝕜) := by
  rw [sum_wedge_right]; congr 1; ext i; rw [← wedge_smul]

private theorem domDomCongr_sum_smul {ι : Type*} {m' n' : ℕ}
    (e : Fin m' ≃ Fin n') (s : Finset ι) (c : ι → 𝕜) (f : ι → M [⋀^Fin m']→L[𝕜] 𝕜) :
    domDomCongr e (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • domDomCongr e (f i) := by
  rw [domDomCongr_sum]; congr 1

private theorem elementaryCovector_assoc {d : ℕ} [FiniteDimensional 𝕜 M] [CompleteSpace 𝕜]
    [CharZero 𝕜]
    (b : Module.Basis (Fin d) 𝕜 (M →L[𝕜] 𝕜))
    (I : Fin m → Fin d) (J : Fin n → Fin d) (K : Fin p → Fin d) :
    domDomCongr Fin.finAssoc.symm
      (wedge_product (elementaryCovector b I)
        (wedge_product (elementaryCovector b J) (elementaryCovector b K)
          (ContinuousLinearMap.mul 𝕜 𝕜)) (ContinuousLinearMap.mul 𝕜 𝕜)) =
    wedge_product (wedge_product (elementaryCovector b I) (elementaryCovector b J)
        (ContinuousLinearMap.mul 𝕜 𝕜)) (elementaryCovector b K)
      (ContinuousLinearMap.mul 𝕜 𝕜) := by
  rw [elementaryCovector_wedge b J K, elementaryCovector_wedge b I (Fin.addCases J K),
      elementaryCovector_wedge b I J, elementaryCovector_wedge b (Fin.addCases I J) K]
  obtain ⟨B, dual⟩ := exists_predual_basis b
  apply toAlternatingMap_injective; apply B.ext_alternating; intro v hv
  show domDomCongr Fin.finAssoc.symm
    (elementaryCovector b (Fin.addCases I (Fin.addCases J K))) (B ∘ v) =
    elementaryCovector b (Fin.addCases (Fin.addCases I J) K) (B ∘ v)
  rw [domDomCongr_apply,
    show (⇑B ∘ v) ∘ ⇑Fin.finAssoc.symm = ⇑B ∘ (v ∘ ⇑Fin.finAssoc.symm) from rfl,
    elementaryCovector_basis_eval B b dual, elementaryCovector_basis_eval B b dual]
  exact Fin.multiKroneckerDelta_addCases_assoc I J K v

/- Associativity of multiplication wedge product -/
theorem wedge_mul_assoc [FiniteDimensional 𝕜 M] [CompleteSpace 𝕜] [CharZero 𝕜]
    (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜)
    (l : M [⋀^Fin p]→L[𝕜] 𝕜) (v : Fin (m + n + p) → M) :
      ContinuousAlternatingMap.domDomCongr
        Fin.finAssoc.symm (g ∧[𝕜] h ∧[𝕜] l) v = ((g ∧[𝕜] h) ∧[𝕜] l) v := by
  suffices h_eq : domDomCongr Fin.finAssoc.symm
        (wedge_product g (wedge_product h l (ContinuousLinearMap.mul 𝕜 𝕜))
          (ContinuousLinearMap.mul 𝕜 𝕜)) =
      wedge_product (wedge_product g h (ContinuousLinearMap.mul 𝕜 𝕜)) l
        (ContinuousLinearMap.mul 𝕜 𝕜) from DFunLike.congr_fun h_eq v
  -- Elementary covector bases for each degree
  set d' := Module.finrank 𝕜 M
  let B : Module.Basis (Fin d') 𝕜 M := Module.finBasis 𝕜 M
  let b : Module.Basis (Fin d') 𝕜 (M →L[𝕜] 𝕜) := B.cDualBasis
  let bm := elementaryCovectorBasis (k := m) B
  let bn := elementaryCovectorBasis (k := n) B
  let bp := elementaryCovectorBasis (k := p) B
  have hbm : ∀ I : Fin m ↪o Fin d', bm I = elementaryCovector b ↑I :=
    fun I => elementaryCovectorBasis_apply B I
  have hbn : ∀ J : Fin n ↪o Fin d', bn J = elementaryCovector b ↑J :=
    fun J => elementaryCovectorBasis_apply B J
  have hbp : ∀ K : Fin p ↪o Fin d', bp K = elementaryCovector b ↑K :=
    fun K => elementaryCovectorBasis_apply B K
  -- Expand g = ∑ c_I • e_I and distribute
  rw [show g = ∑ I, bm.repr g I • bm I from (bm.sum_repr g).symm]; simp only [hbm]
  rw [sum_smul_wedge_left (m := m) (n := n + p), domDomCongr_sum_smul,
      sum_smul_wedge_left (m := m) (n := n),
      sum_smul_wedge_left (m := m + n) (n := p)]
  congr 1; ext I; congr 1
  -- Expand h = ∑ c_J • e_J and distribute
  rw [show h = ∑ J, bn.repr h J • bn J from (bn.sum_repr h).symm]; simp only [hbn]
  rw [sum_smul_wedge_left (m := n) (n := p),
      sum_smul_wedge_right (m := m) (n := n + p), domDomCongr_sum_smul,
      sum_smul_wedge_right (m := m) (n := n),
      sum_smul_wedge_left (m := m + n) (n := p)]
  congr 1; ext J; congr 1
  -- Reduce to single J
  congr 1; ext J; congr 1
  -- Goal: ddc(e_I ∧ (e_J ∧ l)) = (e_I ∧ e_J) ∧ l
  -- Expand l = ∑ c_K • e_K
  rw [show l = ∑ K, bp.repr l K • bp K from (bp.sum_repr l).symm]; simp only [hbp]
  -- Distribute over l-sum
  rw [sum_smul_wedge_right (m := n) (n := p)]
  rw [sum_smul_wedge_right (m := m) (n := n + p)]
  rw [domDomCongr_sum_smul (ι := Fin p ↪o Fin d')]
  rw [sum_smul_wedge_right (m := m + n) (n := p)]
  -- Reduce to single K — use simp_rw to rewrite under binders
  simp_rw [elementaryCovector_assoc b I J]

/- Antisymmetry of wedge product for elementary covectors -/
private theorem elementaryCovector_wedge_antisymm
    [FiniteDimensional 𝕜 M] [CompleteSpace 𝕜] [CharZero 𝕜]
    {d : ℕ} (b : Module.Basis (Fin d) 𝕜 (M →L[𝕜] 𝕜))
    (I : Fin m → Fin d) (J : Fin n → Fin d) :
    ((elementaryCovector b I) ∧[𝕜] (elementaryCovector b J)) =
      ((-1 : 𝕜)^(m*n) •
        ((elementaryCovector b J) ∧[𝕜]
          (elementaryCovector b I))).domDomCongr Fin.finAddCongr := by
  rw [elementaryCovector_wedge b I J, elementaryCovector_wedge b J I]
  obtain ⟨B, dual⟩ := exists_predual_basis b
  apply toAlternatingMap_injective
  apply B.ext_alternating
  intro v hv
  simp only [coe_toAlternatingMap, domDomCongr_apply, smul_apply]
  change (elementaryCovector b (Fin.addCases I J)) (B ∘ v) =
    (-1 : 𝕜)^(m*n) • (elementaryCovector b (Fin.addCases J I)) (B ∘ (v ∘ Fin.finAddCongr))
  rw [elementaryCovector_basis_eval B b dual (Fin.addCases I J) v,
    elementaryCovector_basis_eval B b dual (Fin.addCases J I)
      (v ∘ Fin.finAddCongr)]
  have h_comm := Fin.multiKroneckerDelta_addCases_comm (R := 𝕜) I J v
  simp only [smul_eq_mul]
  rw [h_comm, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/- Antisymmetry of multiplication wedge product -/
theorem wedge_antisymm [FiniteDimensional 𝕜 M] [CompleteSpace 𝕜] [CharZero 𝕜]
    (g : M [⋀^Fin m]→L[𝕜] 𝕜) (h : M [⋀^Fin n]→L[𝕜] 𝕜) :
    (g ∧[𝕜] h) = ((-1 : 𝕜)^(m*n) • (h ∧[𝕜] g)).domDomCongr Fin.finAddCongr := by
  set d' := Module.finrank 𝕜 M
  let B : Module.Basis (Fin d') 𝕜 M := Module.finBasis 𝕜 M
  let b : Module.Basis (Fin d') 𝕜 (M →L[𝕜] 𝕜) := B.cDualBasis
  let bm := elementaryCovectorBasis (k := m) B
  let bn := elementaryCovectorBasis (k := n) B
  have hbm : ∀ I : Fin m ↪o Fin d', bm I = elementaryCovector b ↑I :=
    fun I => elementaryCovectorBasis_apply B I
  have hbn : ∀ J : Fin n ↪o Fin d', bn J = elementaryCovector b ↑J :=
    fun J => elementaryCovectorBasis_apply B J
  nth_rw 1 [show g = ∑ I, bm.repr g I • bm I from (bm.sum_repr g).symm]
  nth_rw 2 [show g = ∑ I, bm.repr g I • bm I from (bm.sum_repr g).symm]
  nth_rw 1 [show h = ∑ J, bn.repr h J • bn J from (bn.sum_repr h).symm]
  nth_rw 2 [show h = ∑ J, bn.repr h J • bn J from (bn.sum_repr h).symm]
  simp only [hbm, hbn]
  simp_rw [sum_smul_wedge_left, sum_smul_wedge_right]
  ext v
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.domDomCongr_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  apply Finset.sum_congr rfl
  intro I _
  have h_anti := DFunLike.congr_fun (elementaryCovector_wedge_antisymm b I J) v
  simp only [ContinuousAlternatingMap.domDomCongr_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h_anti
  rw [h_anti]
  ring

/-- The graded Leibniz rule for `iprod` and wedge product, specialized to elementary covectors. -/
theorem elementaryCovector_iprod_wedge_product
    [FiniteDimensional 𝕜 M] [CompleteSpace 𝕜] [CharZero 𝕜]
    {d : ℕ} (b : Module.Basis (Fin d) 𝕜 (M →L[𝕜] 𝕜))
    (I : Fin (m + 1) → Fin d) (J : Fin (n + 1) → Fin d) (x : M) :
    curryFin (domDomCongr Fin.finAddFlipAssoc
      ((elementaryCovector b I) ∧[𝕜] (elementaryCovector b J))) x =
      (curryFin (elementaryCovector b I) x ∧[𝕜] (elementaryCovector b J)) +
      (-1 : 𝕜) ^ (m + 1) • domDomCongr Fin.finAddFlipAssoc
        ((elementaryCovector b I) ∧[𝕜] curryFin (elementaryCovector b J) x) := by
  -- Step 1: Rewrite wedge products and expand cofactor formulas
  rw [elementaryCovector_wedge b I J,
    curryFin_elementaryCovector b I x, sum_smul_wedge_left]
  simp_rw [elementaryCovector_wedge b _ J]
  rw [curryFin_elementaryCovector b J x, sum_smul_wedge_right]
  simp_rw [elementaryCovector_wedge b I _]
  -- Step 2: Unfold to determinants and Laplace-expand LHS
  ext v; simp only [curryFin_apply, domDomCongr_apply, add_apply, smul_apply,
    sum_apply, smul_eq_mul, elementaryCovector_apply]
  rw [Matrix.det_succ_column_zero]
  simp_rw [show (Fin.cons x v ∘ ⇑Fin.finAddFlipAssoc)
      (0 : Fin ((m + 1) + (n + 1))) = x from by
    simp [Fin.finAddFlipAssoc, finCongr, Fin.cons_zero]]
  -- Step 3: Merge RHS into single sum and match term-by-term
  conv_rhs => rw [Finset.mul_sum]
  rw [show ∀ (f : Fin (m + 1) → 𝕜) (g : Fin (n + 1) → 𝕜),
      (∑ i, f i) + (∑ j, g j) =
      ∑ k, (Fin.addCases f g : Fin ((m + 1) + (n + 1)) → 𝕜) k from fun f g =>
    ((Fin.sum_univ_add (Fin.addCases f g)).symm ▸ by
      simp [Fin.addCases_left, Fin.addCases_right])]
  apply Finset.sum_congr rfl; intro ⟨k, hk⟩ _
  -- Step 4: Split into left (I) and right (J) blocks
  by_cases hlt : k < m + 1
  · -- Left block: addCases picks the I-term
    rw [show (⟨k, hk⟩ : Fin _) = Fin.castAdd (n + 1) ⟨k, hlt⟩ from Fin.ext rfl]
    simp only [Fin.addCases_left, Fin.val_castAdd]
    congr 1
    exact Fin.det_subst_eq (Nat.add_right_comm m 1 n) _ _ (by
      intro i j; simp only [Matrix.submatrix_apply,
        Fin.addCases_succAbove_castAdd I J ⟨k, hlt⟩ i]
      have : ∀ j : Fin (m + n + 1),
          (Fin.cons x v ∘ ⇑(@Fin.finAddFlipAssoc m (n + 1) 1))
            (Fin.succ (Fin.cast (Nat.add_right_comm m 1 n).symm j)) = v j :=
        fun j => by simp [Function.comp, Fin.cons_succ, Fin.finAddFlipAssoc, finCongr]
      simp only [this])
  · -- Right block: addCases picks the J-term with (-1)^(m+1) sign
    have hge := Nat.le_of_not_lt hlt
    set j' : Fin (n + 1) := ⟨k - (m + 1), Nat.sub_lt_left_of_lt_add hge hk⟩
    rw [show (⟨k, hk⟩ : Fin _) = Fin.natAdd (m + 1) j' from
      Fin.ext (Nat.add_sub_cancel' hge).symm]
    simp only [Fin.addCases_right, Fin.val_natAdd]
    rw [pow_add]; ring_nf
    exact congr_arg (- ((b (J j')) x * · * (-1 : 𝕜) ^ m * (-1) ^ j'.val))
      (congr_arg Matrix.det (funext fun i => funext fun j => by
        simp only [Matrix.submatrix_apply,
          Fin.addCases_succAbove_natAdd I J j' i]; congr 1))

/-- The scalar-valued graded Leibniz rule for interior product and wedge product.
Proved by expanding g, h in the elementaryCovector basis and applying
`elementaryCovector_iprod_wedge_product` to each basis pair. -/
theorem iprod_wedge_product_mul [FiniteDimensional 𝕜 M] [CompleteSpace 𝕜] [CharZero 𝕜]
    (g : M [⋀^Fin (m+1)]→L[𝕜] 𝕜) (h : M [⋀^Fin (n+1)]→L[𝕜] 𝕜) (x : M) :
    curryFin (domDomCongr Fin.finAddFlipAssoc (g ∧[𝕜] h)) x =
      (curryFin g x ∧[𝕜] h) +
      (-1 : 𝕜) ^ (m + 1) • domDomCongr Fin.finAddFlipAssoc (g ∧[𝕜] curryFin h x) := by
  -- Step 1: Set up the elementary covector basis.
  set d := Module.finrank 𝕜 M with hd_def
  let B : Module.Basis (Fin d) 𝕜 M := Module.finBasis 𝕜 M
  let b : Module.Basis (Fin d) 𝕜 (M →L[𝕜] 𝕜) := B.cDualBasis
  let basisG : Module.Basis (Fin (m + 1) ↪o Fin d) 𝕜 (M [⋀^Fin (m + 1)]→L[𝕜] 𝕜) :=
    elementaryCovectorBasis B
  let basisH : Module.Basis (Fin (n + 1) ↪o Fin d) 𝕜 (M [⋀^Fin (n + 1)]→L[𝕜] 𝕜) :=
    elementaryCovectorBasis B
  -- basisG / basisH evaluated at I/J equals elementaryCovector b I/J.
  have basisG_eq : ∀ I : Fin (m + 1) ↪o Fin d,
      basisG I = elementaryCovector b ↑I := fun I => elementaryCovectorBasis_apply B I
  have basisH_eq : ∀ J : Fin (n + 1) ↪o Fin d,
      basisH J = elementaryCovector b ↑J := fun J => elementaryCovectorBasis_apply B J
  -- Step 2: Expand g and h in the basis.
  have hg : g = ∑ I : Fin (m + 1) ↪o Fin d, basisG.repr g I • elementaryCovector b ↑I := by
    conv_lhs => rw [← basisG.sum_repr g]
    apply Finset.sum_congr rfl; intro I _
    rw [basisG_eq]
  have hh : h = ∑ J : Fin (n + 1) ↪o Fin d, basisH.repr h J • elementaryCovector b ↑J := by
    conv_lhs => rw [← basisH.sum_repr h]
    apply Finset.sum_congr rfl; intro J _
    rw [basisH_eq]
  -- Step 3: Restate goal as a double sum on each side.
  rw [hg, hh]
  rw [sum_smul_wedge_left]
  -- LHS now: curryFin (domDomCongr finAddFlipAssoc (∑ I, basisG.repr g I • (eI ∧ ∑J, ...))) x
  -- (Actually we need to also distribute the inner sum over the wedge.)
  simp_rw [sum_smul_wedge_right]
  -- LHS: curryFin (domDomCongr finAddFlipAssoc (∑ I, basisG.repr g I •
  --   ∑ J, basisH.repr h J • (eI ∧ eJ))) x
  rw [domDomCongr_sum_smul]
  simp_rw [domDomCongr_sum_smul]
  -- LHS: curryFin (∑ I, basisG.repr g I • ∑ J, basisH.repr h J •
  --   domDomCongr finAddFlipAssoc (eI ∧ eJ)) x
  -- Distribute curryFin over all sums (LHS double sum + RHS occurrences).
  simp_rw [curryFin_sum_smul]
  -- After the simp_rw, the state is:
  -- LHS: ∑ I, c_I • ∑ J, d_J • curryFin (domDomCongr finAddFlipAssoc (eI ∧ eJ)) x
  -- RHS first term: ∑ J, d_J • (∑ I, c_I • curryFin eI x) ∧ eJ
  -- RHS second term: (-1)^(m+1) • domDomCongr finAddFlipAssoc
  --                    (∑ I, c_I • eI ∧ ∑ J, d_J • curryFin eJ x)
  -- Distribute the inner sums in both terms.
  simp_rw [sum_smul_wedge_left, sum_smul_wedge_right]
  -- Distribute domDomCongr over the sums in the second term.
  rw [domDomCongr_sum_smul]
  simp_rw [domDomCongr_sum_smul]
  -- Pull out (-1)^(m+1) into the inner double sum.
  rw [Finset.smul_sum]
  simp_rw [Finset.smul_sum, smul_comm ((-1 : 𝕜) ^ (m + 1))]
  -- Swap the order of summation in the RHS first term so it matches LHS structure.
  rw [Finset.sum_comm
    (f := fun J I => basisH.repr h J •
      basisG.repr g I •
        (curryFin (elementaryCovector b ↑I) x ∧[𝕜] elementaryCovector b ↑J))]
  -- Now combine the two RHS sums.
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro I _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro J _
  -- Goal: c_I • d_J • curryFin (domDomCongr finAddFlipAssoc (eI ∧ eJ)) x =
  --   d_J • c_I • (curryFin eI x ∧ eJ) +
  --   c_I • d_J • (-1)^(m+1) • domDomCongr finAddFlipAssoc (eI ∧ curryFin eJ x)
  -- Bring c_I and d_J to the same side using smul_comm.
  rw [show basisH.repr h J • basisG.repr g I •
      (curryFin (elementaryCovector b ↑I) x ∧[𝕜] elementaryCovector b ↑J) =
      basisG.repr g I • basisH.repr h J •
        (curryFin (elementaryCovector b ↑I) x ∧[𝕜] elementaryCovector b ↑J) from
    smul_comm _ _ _]
  rw [← smul_add, ← smul_add]
  congr 1
  congr 1
  -- Goal: curryFin (domDomCongr finAddFlipAssoc (eI ∧ eJ)) x =
  --   curryFin eI x ∧ eJ + (-1)^(m+1) • domDomCongr finAddFlipAssoc (eI ∧ curryFin eJ x)
  exact elementaryCovector_iprod_wedge_product b I J x

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]

open Fin

-- UNUSED functionality (proof depends on a removed Mathlib lemma
-- `Equiv.Perm.finAddFlip_equiv_eqFin`; sorry'd until the auxiliary
-- equivalence is restored or the lemma is rewritten).
lemma domDomCongr_finAddFlip_wedge_self (g : M [⋀^Fin m]→L[ℝ] ℝ) :
    domDomCongr finAddFlip (g∧[ℝ]g) = (g∧[ℝ]g) := by
  sorry

/- Corollary of `wedge_antisymm` saying that a wedge of g with itself is
zero if m is odd. -/
theorem wedge_self_odd_zero (g : M [⋀^Fin m]→L[ℝ] ℝ) (m_odd : Odd m) :
    (g ∧[ℝ] g) = 0 := by
  let h := wedge_antisymm g g
  rw[Odd.neg_one_pow (Odd.mul m_odd m_odd)] at h
  suffices (g ∧[ℝ] g) = -(g ∧[ℝ] g) by
    rw[← sub_eq_zero, sub_neg_eq_add, DFunLike.ext_iff] at this
    ext x
    simpa using this x
  simp only [finAddCongr, finCongr_refl, neg_smul, one_smul, domDomCongr_refl] at h
  exact h

end wedge

end ContinuousAlternatingMap
