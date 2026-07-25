





import DifferentialGeometry.Tensor.Alternating.Bundle
import DifferentialGeometry.Tensor.Alternating.FDeriv
import DifferentialGeometry.Tensor.Alternating.Wedge
import DifferentialGeometry.Tensor.Exterior.Defs
import DifferentialGeometry.Tensor.Exterior.Congr
import DifferentialGeometry.Tensor.Exterior.Rough
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

namespace DifferentialForm

variable {n m : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem differentiableAt (ω : DifferentialForm n E F) (x : E) :
    DifferentiableAt ℝ ω x :=
  (ω.smooth.differentiable (by norm_cast)).differentiableAt

variable {n m : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

def ederiv (ω : Ω^n⟮E, F⟯) : Ω^(n + 1)⟮E, F⟯ where
  toFun := _root_.ederiv ω.toFun
  smooth := by
    change ContDiff ℝ ⊤ (uncurryFinCLM ∘ fderiv ℝ ω.toFun)
    exact uncurryFinCLM.contDiff.comp (ω.smooth.fderiv_right le_top)

@[simp]
theorem ederiv_toFun (ω : Ω^n⟮E, F⟯) :
    (ederiv ω).toFun = _root_.ederiv ω.toFun := rfl

theorem ederiv_add (ω₁ ω₂ : Ω^n⟮E, F⟯) {x : E} :
    ederiv (ω₁ + ω₂) x = ederiv ω₁ x + ederiv ω₂ x :=
  _root_.ederiv_add ω₁.toFun ω₂.toFun (ω₁.differentiableAt x) (ω₂.differentiableAt x)

theorem ederiv_smul (c : ℝ) (ω : Ω^n⟮E, F⟯) {x : E} :
    ederiv (c • ω) x = c • ederiv ω x :=
  _root_.ederiv_smul ω.toFun c (ω.differentiableAt x)

theorem ederiv_apply (ω : Ω^n⟮E, F⟯) {x : E} (v : Fin (n + 1) → E) :
    ederiv ω x v = ∑ i, (-1) ^ i.val • fderiv ℝ (ω.toFun · (i.removeNth v)) x (v i) :=
  _root_.ederiv_apply ω.toFun (ω.differentiableAt x) v

theorem ederiv_ederiv (ω : Ω^n⟮E, F⟯) : ederiv (ederiv ω) = 0 :=
  ext fun _ => _root_.ederiv_ederiv_apply ω.toFun (ω.smooth.contDiffAt.of_le le_top)

end DifferentialForm

noncomputable def iprod (ω : Ω^(m + 1)⟮E, F⟯) (v : E → E) (hv : ContDiff ℝ ⊤ v) : Ω^m⟮E, F⟯ where
  toFun := fun e => ContinuousAlternatingMap.curryFin (ω e) (v e)
  smooth := by

    have hbl : IsBoundedLinearMap ℝ (curryFin (𝕜 := ℝ) (E := E) (F := F) (n := m)) :=
      ⟨⟨curryFin_add, fun c f => curryFin_smul c f⟩, 1, one_pos, fun g => by
        simp only [one_mul]
        exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g) fun x =>
          ContinuousAlternatingMap.opNorm_le_bound _
            (mul_nonneg (norm_nonneg g) (norm_nonneg x)) fun w => by
              rw [curryFin_apply]; have h := g.le_opNorm (Fin.cons x w)
              simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] at h
              rw [← mul_assoc] at h; exact h⟩
    exact (hbl.contDiff.comp ω.smooth).clm_apply hv

@[simp]
theorem iprod_apply (ω : Ω^(m + 1)⟮E, F⟯) (v : E → E) (hv : ContDiff ℝ ⊤ v) (e : E) :
    iprod ω v hv e = ContinuousAlternatingMap.curryFin (ω e) (v e) :=
  rfl

noncomputable def DifferentialForm.wedge (ω : Ω^m⟮E, F⟯) (τ : Ω^n⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'') : Ω^(m+n)⟮E, F''⟯ where
  toFun := fun x => ω.toFun x ∧[f] τ.toFun x
  smooth := by
    have hω : ContDiff ℝ ⊤ ω.toFun := ω.smooth
    have hτ : ContDiff ℝ ⊤ τ.toFun := τ.smooth
    let wedgeL := ContinuousAlternatingMap.wedge_productL
      (M := E) (m := m) (n := n) f
    change ContDiff ℝ ⊤ (fun x => wedgeL (ω.toFun x) (τ.toFun x))
    exact (wedgeL.contDiff.comp hω).clm_apply hτ

notation ω₁ " ∧["f"] " ω₂ => DifferentialForm.wedge ω₁ ω₂ f
notation ω₁ " ∧ " ω₂ => DifferentialForm.wedge ω₁ ω₂ (ContinuousLinearMap.mul ℝ ℝ)

theorem _root_.ederiv_finset_sum {ι : Type*} {s : Finset ι}
    (ω : ι → (E → E [⋀^Fin n]→L[ℝ] F)) {x : E}
    (hω : ∀ i ∈ s, DifferentiableAt ℝ (ω i) x) :
    _root_.ederiv (∑ i ∈ s, ω i) x = ∑ i ∈ s, _root_.ederiv (ω i) x := by
  change ContinuousAlternatingMap.uncurryFinCLM (fderiv ℝ (∑ i ∈ s, ω i) x) =
    ∑ i ∈ s, ContinuousAlternatingMap.uncurryFinCLM (fderiv ℝ (ω i) x)
  rw [fderiv_sum hω, _root_.map_sum]

theorem basis_expansion [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]
    (basisG : Module.Basis ι ℝ (E [⋀^Fin m]→L[ℝ] ℝ))
    (ω : Ω^m⟮E, ℝ⟯) (y : E) :
    ω y = ∑ I, basisG.equivFun (ω y) I • basisG I :=
  (basisG.sum_equivFun (ω y)).symm

theorem fderiv_mul_scalar (a b : E → ℝ) (y : E)
    (ha : DifferentiableAt ℝ a y) (hb : DifferentiableAt ℝ b y) :
    fderiv ℝ (fun z ↦ a z * b z) y =
      a y • fderiv ℝ b y + b y • fderiv ℝ a y :=
  (ha.hasFDerivAt.mul hb.hasFDerivAt).fderiv

theorem contDiff_basis_coeff [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι]
    (basisG : Module.Basis ι ℝ (E [⋀^Fin m]→L[ℝ] ℝ))
    (ω : Ω^m⟮E, ℝ⟯) (I : ι) :
    ContDiff ℝ ⊤ (fun y ↦ basisG.equivFunL (ω y) I) := by
  letI : Fintype ι := Fintype.ofFinite ι
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) I).comp
    basisG.equivFunL.toContinuousLinearMap).contDiff.comp ω.smooth

theorem _root_.ederiv_smul_const (a : E → ℝ) (e : E [⋀^Fin m]→L[ℝ] ℝ) (y : E)
    (ha : DifferentiableAt ℝ a y) (v : Fin (m + 1) → E) :
    _root_.ederiv (fun z ↦ a z • e) y v =
      ∑ k : Fin (m + 1), (-1 : ℤ) ^ k.val • (fderiv ℝ a y (v k)) • e (k.removeNth v) := by

  have hd : HasFDerivAt (fun z ↦ a z • e) ((fderiv ℝ a y).smulRight e) y :=
    ha.hasFDerivAt.smul_const e

  have hfderiv : fderiv ℝ (fun z ↦ a z • e) y = (fderiv ℝ a y).smulRight e := hd.fderiv

  change ContinuousAlternatingMap.uncurryFin (fderiv ℝ (fun z ↦ a z • e) y) v = _
  rw [hfderiv, ContinuousAlternatingMap.uncurryFin_apply]
  refine Finset.sum_congr rfl fun k _ => ?_

  simp only [ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply]

theorem _root_.ederiv_basis_expansion
    {d : ℕ} [FiniteDimensional ℝ E]
    (B : Module.Basis (Fin d) ℝ E)
    (ω : E → E [⋀^Fin n]→L[ℝ] ℝ) (y : E)
    (hω : DifferentiableAt ℝ ω y) :
    _root_.ederiv ω y =
      ∑ I : Fin n ↪o Fin d,
        fderiv ℝ (fun z => (elementaryCovectorBasis B).repr (ω z) I) y
          ∧₁ ContinuousAlternatingMap.elementaryCovector B.cDualBasis ↑I := by
  sorry

theorem iprod_wedge (ω : Ω^(m + 1)⟮E, F⟯) (τ : Ω^(n + 1)⟮E, F'⟯) (f : F →L[ℝ] F' →L[ℝ] F'')
    (v : E → E) (hv : ContDiff ℝ ⊤ v) :
      iprod (DifferentialForm.domDomCongr Fin.finAddFlipAssoc (ω ∧[f] τ)) v hv = ((iprod ω v hv) ∧[f] τ)
        + (-1 : ℝ)^(m + 1) • (DifferentialForm.domDomCongr Fin.finAddFlipAssoc (ω ∧[f] (iprod τ v hv))) := by
  ext e x
  erw[DifferentialForm.add_apply, ContinuousAlternatingMap.add_apply]
  simp only [Nat.add_eq, iprod_apply, DifferentialForm.domDomCongr_apply, DifferentialForm.smul_apply, coe_smul]
  sorry

namespace DifferentialForm

noncomputable def pullback (f : E → F) (ω : Ω^k⟮F, G⟯) : Ω^k⟮E, G⟯ where
  toFun := fun x ↦ (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)
  smooth := by sorry

@[simp]
theorem pullback_toFun (f : E → F) (ω : Ω^k⟮F, G⟯) :
    (pullback f ω).toFun = RoughDifferentialForm.pullback f ω.toFun := rfl

theorem pullback_ederiv (f : E → F) (ω : Ω^n⟮F, G⟯) {x : E} (hf : ContDiffAt ℝ 2 f x) :
    pullback f (ederiv ω) x = ederiv (pullback f ω) x := by

  sorry

end DifferentialForm

noncomputable section

open Bundle Set Function Filter
open scoped Topology Manifold ContDiff

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  (IM : ModelWithCorners ℝ EM HM)
  (M : Type*) [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]
  {m n : ℕ} {k l : ℕ∞}

notation "Ω^" k "," m "⟮" EM "," IM "," M "⟯" =>
  ContMDiffSection IM (EM [⋀^Fin m]→L[ℝ] ℝ) k
    (Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM : M → Type _) ℝ
      (Bundle.Trivial M ℝ))

namespace DifferentialForm

section mpullback

variable
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN]
  (IN : ModelWithCorners ℝ EN HN)
  (N : Type*) [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ⊤ N]

variable (α β : (x : N) → TangentSpace IN x [⋀^Fin m]→L[ℝ] Trivial N ℝ x)

def mpullback (f : M → N) : (x : M) → TangentSpace IM x [⋀^Fin m]→L[ℝ] Trivial N ℝ (f x) :=
    fun x ↦ (α (f x)).compContinuousLinearMap (mfderiv IM IN f x)

omit [IsManifold IM ω M] [IsManifold IN ω N] in
theorem mpullback_zero (f : M → N) :
    mpullback IM M IN N (0 : (x : N) → TangentSpace IN x [⋀^Fin m]→L[ℝ] Trivial N ℝ x) f = 0 :=
  rfl

omit [IsManifold IM ω M] [IsManifold IN ω N] in
theorem mpullback_add (f : M → N) :
    mpullback IM M IN N (α + β) f = mpullback IM M IN N α f + mpullback IM M IN N β f :=
  rfl

omit [IsManifold IM ω M] [IsManifold IN ω N] in
theorem mpullback_sub (f : M → N) :
    mpullback IM M IN N (α - β) f = mpullback IM M IN N α f - mpullback IM M IN N β f :=
  rfl

omit [IsManifold IM ω M] [IsManifold IN ω N] in
theorem mpullback_neg (f : M → N) :
    - mpullback IM M IN N α f = mpullback IM M IN N (-α) f :=
  rfl

omit [IsManifold IM ω M] [IsManifold IN ω N] in
theorem mpullback_smul (f : M → N) (c : ℝ) :
    c • (mpullback IM M IN N α) f = mpullback IM M IN N (c • α) f :=
  rfl

end mpullback

section minteriorProduct

variable [Π (x : M), NormedAddCommGroup (TangentSpace IM x)]

def minteriorProduct (α : Ω^k,(m + 1)⟮EM,IM,M⟯) (V : Π (x : M), TangentSpace IM x) :
    (x : M) → TangentSpace IM x [⋀^Fin m]→L[ℝ] Trivial M ℝ x := by
  intro x
  let triv_α := trivializationAt (EM [⋀^Fin (m + 1)]→L[ℝ] ℝ) ⋀^Fin (m + 1)⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
  let α_local := (triv_α ⟨x, α x⟩).2
  let ip_local := ContinuousAlternatingMap.curryFin α_local (V x)
  let triv_ip := trivializationAt (EM [⋀^Fin m]→L[ℝ] ℝ) ⋀^Fin m⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
  exact triv_ip.symm x ip_local

end minteriorProduct

section mwedgeProduct

variable
  [Π (x : M), NormedAddCommGroup (TangentSpace IM x)]

def mwedgeProduct (α : Ω^k,m⟮EM,IM,M⟯) (β : Ω^l,n⟮EM,IM,M⟯) :
    (x : M) → TangentSpace IM x [⋀^Fin (m + n)]→L[ℝ] Trivial M ℝ x := by
  intro x
  let triv_α := trivializationAt (EM [⋀^Fin m]→L[ℝ] ℝ) ⋀^Fin m⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
  let triv_β := trivializationAt (EM [⋀^Fin n]→L[ℝ] ℝ) ⋀^Fin n⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
  let α_local := (triv_α ⟨x, α x⟩).2
  let β_local := (triv_β ⟨x, β x⟩).2
  let wedge_local := ContinuousAlternatingMap.wedge_product α_local β_local (ContinuousLinearMap.mul ℝ ℝ)
  let triv_wedge := trivializationAt (EM [⋀^Fin (m + n)]→L[ℝ] ℝ) ⋀^Fin (m + n)⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
  exact triv_wedge.symm x wedge_local

end mwedgeProduct

section mederiv

variable (α : Ω^k,m⟮EM,IM,M⟯)

def mederivWithin (s : Set M) (x : M) : TangentSpace IM x [⋀^Fin (m + 1)]→L[ℝ] Trivial M ℝ x :=
  let triv_α := trivializationAt (EM [⋀^Fin m]→L[ℝ] ℝ) ⋀^Fin m⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
  let α_local (e : EM) := (triv_α ⟨(extChartAt IM x).symm e, α ((extChartAt IM x).symm e)⟩).2
  let s_local := (extChartAt IM x).symm ⁻¹' s ∩ range IM
  let dα_local := ederivWithin α_local s_local
  let triv_dα := trivializationAt (EM [⋀^Fin (m + 1)]→L[ℝ] ℝ) ⋀^Fin (m + 1)⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
  triv_dα.symm x (dα_local (extChartAt IM x x))

lemma mederivWithin_def (s : Set M) :
  mederivWithin IM M α s = fun x ↦
    let triv_α := trivializationAt (EM [⋀^Fin m]→L[ℝ] ℝ) ⋀^Fin m⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
    let α_local (e : EM) := (triv_α ⟨(extChartAt IM x).symm e, α ((extChartAt IM x).symm e)⟩).2
    let s_local := (extChartAt IM x).symm ⁻¹' s ∩ range IM
    let dα_local := ederivWithin α_local s_local
    let triv_dα := trivializationAt (EM [⋀^Fin (m + 1)]→L[ℝ] ℝ) ⋀^Fin (m + 1)⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
    triv_dα.symm x (dα_local (extChartAt IM x x)) :=
  rfl

lemma mederivWithin_apply (s : Set M) (x : M) :
  mederivWithin IM M α s x =
    let triv_α := trivializationAt (EM [⋀^Fin m]→L[ℝ] ℝ) ⋀^Fin m⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
    let α_local (e : EM) := (triv_α ⟨(extChartAt IM x).symm e, α ((extChartAt IM x).symm e)⟩).2
    let s_local := (extChartAt IM x).symm ⁻¹' s ∩ range IM
    let dα_local := ederivWithin α_local s_local
    let triv_dα := trivializationAt (EM [⋀^Fin (m + 1)]→L[ℝ] ℝ) ⋀^Fin (m + 1)⟮ℝ; EM, TangentSpace IM; ℝ, Bundle.Trivial M ℝ⟯ x
    triv_dα.symm x (dα_local (extChartAt IM x x)) :=
  rfl

def mederiv (x : M) : TangentSpace IM x [⋀^Fin (m + 1)]→L[ℝ] Trivial M ℝ x :=
    mederivWithin IM M α univ x

lemma mederiv_def : mederiv IM M α = fun x ↦ mederiv IM M α x :=
  rfl

theorem mederivWithin_univ : mederivWithin IM M α univ = mederiv IM M α :=
  rfl

end mederiv

end DifferentialForm
