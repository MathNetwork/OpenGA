import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import DifferentialGeometry.Bundle.Equiv
import DifferentialGeometry.Bundle.Frame
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.TensorNabla.CotangentExtension
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorExtension


noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

section mkHom₃

variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
variable {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] [FiniteDimensional ℝ F₃]
variable {V₁ : M → Type*} [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁] [ContMDiffVectorBundle 1 F₁ V₁ I]
variable {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂] [ContMDiffVectorBundle 1 F₂ V₂ I]
variable {V₃ : M → Type*} [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)]
  [∀ x, TopologicalSpace (V₃ x)] [TopologicalSpace (TotalSpace F₃ V₃)]
  [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃] [ContMDiffVectorBundle 1 F₃ V₃ I]

private noncomputable def mkHom₃FirstSlot
    (Φ : (Π x : M, V₁ x) → (Π x : M, V₂ x) → (Π x : M, V₃ x) → ℝ) (x : M)
    (hΦ₁ : ∀ σ₂ σ₃, MDiffAt (T% σ₂) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₁ (Φ · σ₂ σ₃) x)
    (hΦ₂ : ∀ σ₁ σ₃, MDiffAt (T% σ₁) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₂ (Φ σ₁ · σ₃) x)
    (hΦ₃ : ∀ σ₁ σ₂, MDiffAt (T% σ₁) x → MDiffAt (T% σ₂) x →
      TensorialAt I F₃ (Φ σ₁ σ₂) x) :
    V₁ x →ₗ[ℝ] (V₂ x →L[ℝ] V₃ x →L[ℝ] ℝ) where
  toFun v :=
    TensorialAt.mkHom₂ (Φ (FiberBundle.extend F₁ v)) x
      (fun σ₃ hσ₃ => hΦ₂ (FiberBundle.extend F₁ v) σ₃ (mdifferentiableAt_extend ..) hσ₃)
      (fun σ₂ hσ₂ => hΦ₃ (FiberBundle.extend F₁ v) σ₂ (mdifferentiableAt_extend ..) hσ₂)
  map_add' v v' := by
    classical
    ext y z
    set σ₂ : Π x : M, V₂ x := FiberBundle.extend F₂ y
    set σ₃ : Π x : M, V₃ x := FiberBundle.extend F₃ z
    have hσ₂ : MDiffAt (T% σ₂) x := mdifferentiableAt_extend ..
    have hσ₃ : MDiffAt (T% σ₃) x := mdifferentiableAt_extend ..
    have hσ₂x : σ₂ x = y := FiberBundle.extend_apply_self F₂ y
    have hσ₃x : σ₃ x = z := FiberBundle.extend_apply_self F₃ z
    rw [show y = σ₂ x from hσ₂x.symm, show z = σ₃ x from hσ₃x.symm]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
    simp only [TensorialAt.mkHom₂_apply _ _ hσ₂ hσ₃]
    have h1 : (FiberBundle.extend F₁ (v + v') : Π x : M, V₁ x) x = v + v' :=
      FiberBundle.extend_apply_self F₁ (v + v')
    have h2 : (FiberBundle.extend F₁ v : Π x : M, V₁ x) x = v :=
      FiberBundle.extend_apply_self F₁ v
    have h3 : (FiberBundle.extend F₁ v' : Π x : M, V₁ x) x = v' :=
      FiberBundle.extend_apply_self F₁ v'
    set τ : Π x : M, V₁ x :=
      (FiberBundle.extend F₁ v : Π x : M, V₁ x) + FiberBundle.extend F₁ v' with hτ_def
    have hτ : MDiffAt (T% τ) x :=
      mdifferentiableAt_add_section (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
    have hτx : τ x = v + v' := by
      change (FiberBundle.extend F₁ v : Π x : M, V₁ x) x
        + (FiberBundle.extend F₁ v' : Π x : M, V₁ x) x = v + v'
      rw [h2, h3]
    have hpt := (hΦ₁ σ₂ σ₃ hσ₂ hσ₃).pointwise
      (mdifferentiableAt_extend ..) hτ (by rw [h1, hτx])
    rw [hpt]
    rw [hτ_def, (hΦ₁ σ₂ σ₃ hσ₂ hσ₃).add (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)]
  map_smul' c v := by
    classical
    ext y z
    set σ₂ : Π x : M, V₂ x := FiberBundle.extend F₂ y
    set σ₃ : Π x : M, V₃ x := FiberBundle.extend F₃ z
    have hσ₂ : MDiffAt (T% σ₂) x := mdifferentiableAt_extend ..
    have hσ₃ : MDiffAt (T% σ₃) x := mdifferentiableAt_extend ..
    have hσ₂x : σ₂ x = y := FiberBundle.extend_apply_self F₂ y
    have hσ₃x : σ₃ x = z := FiberBundle.extend_apply_self F₃ z
    rw [show y = σ₂ x from hσ₂x.symm, show z = σ₃ x from hσ₃x.symm]
    rw [RingHom.id_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    simp only [TensorialAt.mkHom₂_apply _ _ hσ₂ hσ₃]
    have h1 : (FiberBundle.extend F₁ (c • v) : Π x : M, V₁ x) x = c • v :=
      FiberBundle.extend_apply_self F₁ (c • v)
    have h2 : (FiberBundle.extend F₁ v : Π x : M, V₁ x) x = v :=
      FiberBundle.extend_apply_self F₁ v
    set τ : Π x : M, V₁ x := (fun _ : M => c) • (FiberBundle.extend F₁ v : Π x : M, V₁ x)
      with hτ_def
    have hτ : MDiffAt (T% τ) x :=
      (mdifferentiableAt_const (c := c)).smul_section (mdifferentiableAt_extend ..)
    have hτx : τ x = c • v := by
      change c • (FiberBundle.extend F₁ v : Π x : M, V₁ x) x = c • v
      rw [h2]
    have hpt := (hΦ₁ σ₂ σ₃ hσ₂ hσ₃).pointwise
      (mdifferentiableAt_extend ..) hτ (by rw [h1, hτx])
    rw [hpt]
    rw [hτ_def, (hΦ₁ σ₂ σ₃ hσ₂ hσ₃).smul (f := fun _ => c) (mdifferentiable_const ..)
        (mdifferentiableAt_extend ..)]

noncomputable def mkHom₃
    (Φ : (Π x : M, V₁ x) → (Π x : M, V₂ x) → (Π x : M, V₃ x) → ℝ) (x : M)
    (hΦ₁ : ∀ σ₂ σ₃, MDiffAt (T% σ₂) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₁ (Φ · σ₂ σ₃) x)
    (hΦ₂ : ∀ σ₁ σ₃, MDiffAt (T% σ₁) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₂ (Φ σ₁ · σ₃) x)
    (hΦ₃ : ∀ σ₁ σ₂, MDiffAt (T% σ₁) x → MDiffAt (T% σ₂) x →
      TensorialAt I F₃ (Φ σ₁ σ₂) x) :
    V₁ x →L[ℝ] V₂ x →L[ℝ] V₃ x →L[ℝ] ℝ :=
  have : T2Space (V₁ x) := FiberBundle.t2Space F₁ V₁ x
  have : FiniteDimensional ℝ (V₁ x) := VectorBundle.finiteDimensional ℝ F₁ V₁ x
  have : IsTopologicalAddGroup (V₁ x) :=
    (VectorBundle.continuousLinearEquivAt ℝ F₁ V₁ x).toContinuousAddEquiv.isTopologicalAddGroup
  have : ContinuousSMul ℝ (V₁ x) :=
    (VectorBundle.continuousLinearEquivAt ℝ F₁ V₁ x).continuousSMul
  LinearMap.toContinuousLinearMap (mkHom₃FirstSlot Φ x hΦ₁ hΦ₂ hΦ₃)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
theorem mkHom₃_apply
    {Φ : (Π x : M, V₁ x) → (Π x : M, V₂ x) → (Π x : M, V₃ x) → ℝ} {x : M}
    (hΦ₁ : ∀ σ₂ σ₃, MDiffAt (T% σ₂) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₁ (Φ · σ₂ σ₃) x)
    (hΦ₂ : ∀ σ₁ σ₃, MDiffAt (T% σ₁) x → MDiffAt (T% σ₃) x →
      TensorialAt I F₂ (Φ σ₁ · σ₃) x)
    (hΦ₃ : ∀ σ₁ σ₂, MDiffAt (T% σ₁) x → MDiffAt (T% σ₂) x →
      TensorialAt I F₃ (Φ σ₁ σ₂) x)
    {σ₁ : Π x : M, V₁ x} {σ₂ : Π x : M, V₂ x} {σ₃ : Π x : M, V₃ x}
    (hσ₁ : MDiffAt (T% σ₁) x) (hσ₂ : MDiffAt (T% σ₂) x) (hσ₃ : MDiffAt (T% σ₃) x) :
    mkHom₃ Φ x hΦ₁ hΦ₂ hΦ₃ (σ₁ x) (σ₂ x) (σ₃ x) = Φ σ₁ σ₂ σ₃ := by
  classical
  have hcoe : (mkHom₃ Φ x hΦ₁ hΦ₂ hΦ₃) (σ₁ x) =
      mkHom₃FirstSlot Φ x hΦ₁ hΦ₂ hΦ₃ (σ₁ x) := rfl
  rw [hcoe]
  have hstep : (mkHom₃FirstSlot Φ x hΦ₁ hΦ₂ hΦ₃ (σ₁ x)) (σ₂ x) (σ₃ x) =
      Φ (FiberBundle.extend F₁ (σ₁ x)) σ₂ σ₃ := by
    change (TensorialAt.mkHom₂ (Φ (FiberBundle.extend F₁ (σ₁ x))) x
      (fun σ₃ hσ₃ => hΦ₂ (FiberBundle.extend F₁ (σ₁ x)) σ₃ (mdifferentiableAt_extend ..) hσ₃)
      (fun σ₂ hσ₂ => hΦ₃ (FiberBundle.extend F₁ (σ₁ x)) σ₂ (mdifferentiableAt_extend ..) hσ₂))
      (σ₂ x) (σ₃ x) = _
    exact TensorialAt.mkHom₂_apply _ _ hσ₂ hσ₃
  rw [hstep]
  exact (hΦ₁ σ₂ σ₃ hσ₂ hσ₃).pointwise (mdifferentiableAt_extend ..) hσ₁ (by simp)

end mkHom₃

local instance tensor03FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  inferInstance

local instance tensor03VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  inferInstance

local instance tensor03ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  inferInstance

def MDiffAtTensor03
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ))
    (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M =>
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (T b)) x

def tensor03Scalar
    (cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M)
    (X Y Z W : Π x : M, TangentSpace I x) : ℝ :=
  extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x (X x)
    - T x (cov Y x (X x)) (Z x) (W x)
    - T x (Y x) (cov Z x (X x)) (W x)
    - T x (Y x) (Z x) (cov W x (X x))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma mdifferentiableAt_tensor03_apply_one
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {Y : Π x : M, TangentSpace I x} {x : M}
    (hT : MDiffAtTensor03 T x) (hY : MDiffAt (T% Y) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (T b (Y b))) x :=
  MDifferentiableAt.clm_bundle_apply
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (b := fun b : M => b)
    (ϕ := fun b => T b) (v := fun b => Y b) hT hY

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma mdifferentiableAt_tensor03_apply_two
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hT : MDiffAtTensor03 T x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (T b (Y b) (Z b))) x :=
  MDifferentiableAt.clm_bundle_apply
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (b := fun b : M => b)
    (ϕ := fun b => T b (Y b)) (v := fun b => Z b)
    (mdifferentiableAt_tensor03_apply_one hT hY) hZ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma mdifferentiableAt_tensor03_pairing
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hT : MDiffAtTensor03 T x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hW : MDiffAt (T% W) x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b) (W b)) x := by
  have h2 : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun m => TotalSpace.mk' ℝ (E := fun _ : M => ℝ) m (T m (Y m) (Z m) (W m))) x :=
    MDifferentiableAt.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun _ : M => ℝ)
      (b := fun b : M => b)
      (ϕ := fun b => T b (Y b) (Z b)) (v := fun b => W b)
      (mdifferentiableAt_tensor03_apply_two hT hY hZ) hW
  rw [mdifferentiableAt_totalSpace] at h2
  exact h2.2

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma tensor03Scalar_tensorialAt_X
    (_covOn : IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (cov : (Π x : M, TangentSpace I x) →
        (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)) Set.univ)
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x : M) (Y Z W : Π x : M, TangentSpace I x)
    (_hY : MDiffAt (T% Y) x) (_hZ : MDiffAt (T% Z) x) (_hW : MDiffAt (T% W) x) :
    TensorialAt I E (tensor03Scalar cov T x · Y Z W) x where
  smul {f X} _hf _hX := by
    classical
    unfold tensor03Scalar
    have hfX : (f • X) x = f x • X x := rfl
    rw [hfX]
    rw [(extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x).map_smul]
    rw [(cov.toFun Y x).map_smul, (cov.toFun Z x).map_smul, (cov.toFun W x).map_smul]
    rw [(T x).map_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul]
    rw [smul_sub, smul_sub, smul_sub]
  add {X X'} _hX _hX' := by
    classical
    unfold tensor03Scalar
    have hXX' : (X + X') x = X x + X' x := rfl
    rw [hXX']
    rw [map_add, (cov.toFun Y x).map_add, (cov.toFun Z x).map_add, (cov.toFun W x).map_add]
    rw [(T x).map_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.map_add]
    abel

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma tensor03Scalar_tensorialAt_Y
    (covOn : IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (cov : (Π x : M, TangentSpace I x) →
        (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)) Set.univ)
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hT : MDiffAtTensor03 T x)
    (X : Π x : M, TangentSpace I x) (_hX : MDiffAt (T% X) x)
    (Z W : Π x : M, TangentSpace I x) (hZ : MDiffAt (T% Z) x) (hW : MDiffAt (T% W) x) :
    TensorialAt I E (tensor03Scalar cov T x X · Z W) x where
  smul {g Y} hg hY := by
    classical
    set h : M → ℝ := fun b => T b (Y b) (Z b) (W b) with hh_def
    have hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ hW
    have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g x := hg
    have hfun : (fun b : M => T b ((g • Y) b) (Z b) (W b)) = (fun b : M => g b * h b) := by
      funext b
      change T b ((g • Y) b) (Z b) (W b) = g b * h b
      have : (g • Y) b = g b • Y b := rfl
      rw [this, ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
    change extDerivFun (I := I) (fun b => T b ((g • Y) b) (Z b) (W b)) x (X x)
        - T x (cov.toFun (g • Y) x (X x)) (Z x) (W x)
        - T x ((g • Y) x) (cov.toFun Z x (X x)) (W x)
        - T x ((g • Y) x) (Z x) (cov.toFun W x (X x)) =
      g x • (extDerivFun (I := I) h x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x)))
    rw [hfun, extDerivFun_mul_apply hg' hh, covOn.leibniz hY hg (Set.mem_univ x)]
    have h_gY_x : (g • Y) x = g x • Y x := rfl
    rw [h_gY_x]
    have hhx : h x = T x (Y x) (Z x) (W x) := rfl
    rw [hhx]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  add {Y Y'} hY hY' := by
    classical
    change extDerivFun (I := I) (fun b => T b ((Y + Y') b) (Z b) (W b)) x (X x)
        - T x (cov.toFun (Y + Y') x (X x)) (Z x) (W x)
        - T x ((Y + Y') x) (cov.toFun Z x (X x)) (W x)
        - T x ((Y + Y') x) (Z x) (cov.toFun W x (X x)) =
      (extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x))) +
      (extDerivFun (I := I) (fun b => T b (Y' b) (Z b) (W b)) x (X x)
        - T x (cov.toFun Y' x (X x)) (Z x) (W x)
        - T x (Y' x) (cov.toFun Z x (X x)) (W x)
        - T x (Y' x) (Z x) (cov.toFun W x (X x)))
    have hadd_fun : (fun b : M => T b ((Y + Y') b) (Z b) (W b)) =
        (fun b : M => T b (Y b) (Z b) (W b)) + (fun b : M => T b (Y' b) (Z b) (W b)) := by
      funext b
      change T b ((Y + Y') b) (Z b) (W b) = T b (Y b) (Z b) (W b) + T b (Y' b) (Z b) (W b)
      have : (Y + Y') b = Y b + Y' b := rfl
      rw [this, ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.add_apply]
    have h1 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ hW
    have h2 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y' b) (Z b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT hY' hZ hW
    have hext_add : extDerivFun (I := I) (fun b => T b ((Y + Y') b) (Z b) (W b)) x =
        extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x +
        extDerivFun (I := I) (fun b => T b (Y' b) (Z b) (W b)) x := by
      rw [hadd_fun, extDerivFun_add h1 h2]
    rw [hext_add]
    rw [covOn.add hY hY' (Set.mem_univ x)]
    have h_YY' : (Y + Y') x = Y x + Y' x := rfl
    rw [h_YY']
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
    abel

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma tensor03Scalar_tensorialAt_Z
    (covOn : IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (cov : (Π x : M, TangentSpace I x) →
        (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)) Set.univ)
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hT : MDiffAtTensor03 T x)
    (X : Π x : M, TangentSpace I x) (_hX : MDiffAt (T% X) x)
    (Y W : Π x : M, TangentSpace I x) (hY : MDiffAt (T% Y) x) (hW : MDiffAt (T% W) x) :
    TensorialAt I E (tensor03Scalar cov T x X Y · W) x where
  smul {g Z} hg hZ := by
    classical
    set h : M → ℝ := fun b => T b (Y b) (Z b) (W b) with hh_def
    have hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ hW
    have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g x := hg
    have hfun : (fun b : M => T b (Y b) ((g • Z) b) (W b)) = (fun b : M => g b * h b) := by
      funext b
      change T b (Y b) ((g • Z) b) (W b) = g b * h b
      have : (g • Z) b = g b • Z b := rfl
      rw [this, ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    change extDerivFun (I := I) (fun b => T b (Y b) ((g • Z) b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) ((g • Z) x) (W x)
        - T x (Y x) (cov.toFun (g • Z) x (X x)) (W x)
        - T x (Y x) ((g • Z) x) (cov.toFun W x (X x)) =
      g x • (extDerivFun (I := I) h x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x)))
    rw [hfun, extDerivFun_mul_apply hg' hh, covOn.leibniz hZ hg (Set.mem_univ x)]
    have h_gZ_x : (g • Z) x = g x • Z x := rfl
    rw [h_gZ_x]
    have hhx : h x = T x (Y x) (Z x) (W x) := rfl
    rw [hhx]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  add {Z Z'} hZ hZ' := by
    classical
    change extDerivFun (I := I) (fun b => T b (Y b) ((Z + Z') b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) ((Z + Z') x) (W x)
        - T x (Y x) (cov.toFun (Z + Z') x (X x)) (W x)
        - T x (Y x) ((Z + Z') x) (cov.toFun W x (X x)) =
      (extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x))) +
      (extDerivFun (I := I) (fun b => T b (Y b) (Z' b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z' x) (W x)
        - T x (Y x) (cov.toFun Z' x (X x)) (W x)
        - T x (Y x) (Z' x) (cov.toFun W x (X x)))
    have hadd_fun : (fun b : M => T b (Y b) ((Z + Z') b) (W b)) =
        (fun b : M => T b (Y b) (Z b) (W b)) + (fun b : M => T b (Y b) (Z' b) (W b)) := by
      funext b
      change T b (Y b) ((Z + Z') b) (W b) = T b (Y b) (Z b) (W b) + T b (Y b) (Z' b) (W b)
      have : (Z + Z') b = Z b + Z' b := rfl
      rw [this, ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply]
    have h1 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ hW
    have h2 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z' b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ' hW
    have hext_add : extDerivFun (I := I) (fun b => T b (Y b) ((Z + Z') b) (W b)) x =
        extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x +
        extDerivFun (I := I) (fun b => T b (Y b) (Z' b) (W b)) x := by
      rw [hadd_fun, extDerivFun_add h1 h2]
    rw [hext_add]
    rw [covOn.add hZ hZ' (Set.mem_univ x)]
    have h_ZZ' : (Z + Z') x = Z x + Z' x := rfl
    rw [h_ZZ']
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
    abel

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma tensor03Scalar_tensorialAt_W
    (covOn : IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (cov : (Π x : M, TangentSpace I x) →
        (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)) Set.univ)
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hT : MDiffAtTensor03 T x)
    (X : Π x : M, TangentSpace I x) (_hX : MDiffAt (T% X) x)
    (Y Z : Π x : M, TangentSpace I x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (tensor03Scalar cov T x X Y Z) x where
  smul {g W} hg hW := by
    classical
    set h : M → ℝ := fun b => T b (Y b) (Z b) (W b) with hh_def
    have hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ hW
    have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g x := hg
    have hfun : (fun b : M => T b (Y b) (Z b) ((g • W) b)) = (fun b : M => g b * h b) := by
      funext b
      change T b (Y b) (Z b) ((g • W) b) = g b * h b
      have : (g • W) b = g b • W b := rfl
      rw [this, ContinuousLinearMap.map_smul, smul_eq_mul]
    change extDerivFun (I := I) (fun b => T b (Y b) (Z b) ((g • W) b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) ((g • W) x)
        - T x (Y x) (cov.toFun Z x (X x)) ((g • W) x)
        - T x (Y x) (Z x) (cov.toFun (g • W) x (X x)) =
      g x • (extDerivFun (I := I) h x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x)))
    rw [hfun, extDerivFun_mul_apply hg' hh, covOn.leibniz hW hg (Set.mem_univ x)]
    have h_gW_x : (g • W) x = g x • W x := rfl
    rw [h_gW_x]
    have hhx : h x = T x (Y x) (Z x) (W x) := rfl
    rw [hhx]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.map_add,
      ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  add {W W'} hW hW' := by
    classical
    change extDerivFun (I := I) (fun b => T b (Y b) (Z b) ((W + W') b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) ((W + W') x)
        - T x (Y x) (cov.toFun Z x (X x)) ((W + W') x)
        - T x (Y x) (Z x) (cov.toFun (W + W') x (X x)) =
      (extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x))) +
      (extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W' b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W' x)
        - T x (Y x) (cov.toFun Z x (X x)) (W' x)
        - T x (Y x) (Z x) (cov.toFun W' x (X x)))
    have hadd_fun : (fun b : M => T b (Y b) (Z b) ((W + W') b)) =
        (fun b : M => T b (Y b) (Z b) (W b)) + (fun b : M => T b (Y b) (Z b) (W' b)) := by
      funext b
      change T b (Y b) (Z b) ((W + W') b) = T b (Y b) (Z b) (W b) + T b (Y b) (Z b) (W' b)
      have : (W + W') b = W b + W' b := rfl
      rw [this, ContinuousLinearMap.map_add]
    have h1 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ hW
    have h2 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b) (W' b)) x :=
      mdifferentiableAt_tensor03_pairing hT hY hZ hW'
    have hext_add : extDerivFun (I := I) (fun b => T b (Y b) (Z b) ((W + W') b)) x =
        extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x +
        extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W' b)) x := by
      rw [hadd_fun, extDerivFun_add h1 h2]
    rw [hext_add]
    rw [covOn.add hW hW' (Set.mem_univ x)]
    have h_WW' : (W + W') x = W x + W' x := rfl
    rw [h_WW']
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add]
    abel

private noncomputable def tensor03TrilinAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (v : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  mkHom₃ (fun Y Z W => tensor03Scalar (cov.toFun) T x (FiberBundle.extend E v) Y Z W) x
    (fun Z W hZ hW =>
      tensor03Scalar_tensorialAt_Y cov.isCovariantDerivativeOnUniv hT
        (FiberBundle.extend E v) (mdifferentiableAt_extend ..) Z W hZ hW)
    (fun Y W hY hW =>
      tensor03Scalar_tensorialAt_Z cov.isCovariantDerivativeOnUniv hT
        (FiberBundle.extend E v) (mdifferentiableAt_extend ..) Y W hY hW)
    (fun Y Z hY hZ =>
      tensor03Scalar_tensorialAt_W cov.isCovariantDerivativeOnUniv hT
        (FiberBundle.extend E v) (mdifferentiableAt_extend ..) Y Z hY hZ)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma tensor03TrilinAt_apply_extend
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (v : TangentSpace I x)
    {Y Z W : Π x : M, TangentSpace I x}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hW : MDiffAt (T% W) x) :
    tensor03TrilinAt cov hT v (Y x) (Z x) (W x) =
      tensor03Scalar (cov.toFun) T x (FiberBundle.extend E v) Y Z W := by
  classical
  unfold tensor03TrilinAt
  exact mkHom₃_apply _ _ _ hY hZ hW

private noncomputable def tensor03XSlot
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) :
    TangentSpace I x →ₗ[ℝ]
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) where
  toFun v := tensor03TrilinAt cov hT v
  map_add' v v' := by
    classical
    ext y z w
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    set Z : Π x : M, TangentSpace I x := FiberBundle.extend E z
    set W : Π x : M, TangentSpace I x := FiberBundle.extend E w
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
    have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend ..
    have hW : MDiffAt (T% W) x := mdifferentiableAt_extend ..
    have hYx : Y x = y := FiberBundle.extend_apply_self E y
    have hZx : Z x = z := FiberBundle.extend_apply_self E z
    have hWx : W x = w := FiberBundle.extend_apply_self E w
    rw [show y = Y x from hYx.symm, show z = Z x from hZx.symm, show w = W x from hWx.symm]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.add_apply]
    rw [tensor03TrilinAt_apply_extend cov hT (v + v') hY hZ hW,
        tensor03TrilinAt_apply_extend cov hT v hY hZ hW,
        tensor03TrilinAt_apply_extend cov hT v' hY hZ hW]
    have h1 : (FiberBundle.extend E (v + v') : Π x : M, TangentSpace I x) x = v + v' :=
      FiberBundle.extend_apply_self E (v + v')
    have h2 : (FiberBundle.extend E v : Π x : M, TangentSpace I x) x = v :=
      FiberBundle.extend_apply_self E v
    have h3 : (FiberBundle.extend E v' : Π x : M, TangentSpace I x) x = v' :=
      FiberBundle.extend_apply_self E v'
    unfold tensor03Scalar
    rw [h1, h2, h3]
    rw [(extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x).map_add]
    rw [(cov.toFun Y x).map_add, (cov.toFun Z x).map_add, (cov.toFun W x).map_add]
    rw [(T x).map_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.map_add]
    abel
  map_smul' c v := by
    classical
    ext y z w
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    set Z : Π x : M, TangentSpace I x := FiberBundle.extend E z
    set W : Π x : M, TangentSpace I x := FiberBundle.extend E w
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
    have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend ..
    have hW : MDiffAt (T% W) x := mdifferentiableAt_extend ..
    have hYx : Y x = y := FiberBundle.extend_apply_self E y
    have hZx : Z x = z := FiberBundle.extend_apply_self E z
    have hWx : W x = w := FiberBundle.extend_apply_self E w
    rw [show y = Y x from hYx.symm, show z = Z x from hZx.symm, show w = W x from hWx.symm]
    rw [RingHom.id_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply]
    rw [tensor03TrilinAt_apply_extend cov hT (c • v) hY hZ hW,
        tensor03TrilinAt_apply_extend cov hT v hY hZ hW]
    have h1 : (FiberBundle.extend E (c • v) : Π x : M, TangentSpace I x) x = c • v :=
      FiberBundle.extend_apply_self E (c • v)
    have h2 : (FiberBundle.extend E v : Π x : M, TangentSpace I x) x = v :=
      FiberBundle.extend_apply_self E v
    unfold tensor03Scalar
    rw [h1, h2]
    rw [(extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x).map_smul]
    rw [(cov.toFun Y x).map_smul, (cov.toFun Z x).map_smul, (cov.toFun W x).map_smul]
    rw [(T x).map_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul]
    simp only [smul_eq_mul]
    ring

def tensor03CovAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x : M) :
    TangentSpace I x →L[ℝ]
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  classical
  by_cases hT : MDiffAtTensor03 T x
  · exact LinearMap.toContinuousLinearMap (tensor03XSlot cov hT)
  · exact 0

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma tensor03CovAt_apply_of_diff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (v : TangentSpace I x) :
    tensor03CovAt cov T x v = tensor03TrilinAt cov hT v := by
  classical
  unfold tensor03CovAt
  rw [dif_pos hT]
  rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma tensor03CovAt_apply_of_diff_extend
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) {X Y Z W : Π x : M, TangentSpace I x}
    (_hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (hW : MDiffAt (T% W) x) :
    tensor03CovAt cov T x (X x) (Y x) (Z x) (W x) =
      tensor03Scalar (cov.toFun) T x X Y Z W := by
  classical
  rw [tensor03CovAt_apply_of_diff cov hT (X x)]
  rw [tensor03TrilinAt_apply_extend cov hT (X x) hY hZ hW]
  unfold tensor03Scalar
  have hext : (FiberBundle.extend E (X x) : Π x : M, TangentSpace I x) x = X x :=
    FiberBundle.extend_apply_self E (X x)
  rw [hext]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensor03CovAt_of_not_diff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : ¬ MDiffAtTensor03 T x) :
    tensor03CovAt cov T x = 0 := by
  classical
  unfold tensor03CovAt
  rw [dif_neg hT]

def tensor03CovFun
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) →
      (Π x : M, TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  fun T x => tensor03CovAt cov T x

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensor03CovFun_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x : M) :
    tensor03CovFun cov T x = tensor03CovAt cov T x := rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma tensor03CovFun_isCovariantDerivativeOn
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    IsCovariantDerivativeOn (V := (fun x : M =>
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (tensor03CovFun cov) Set.univ where
  add {T T'} {x} hT hT' _hx := by
    classical
    have hT_t : MDiffAtTensor03 T x := hT
    have hT'_t : MDiffAtTensor03 T' x := hT'
    have hsum_T : MDiffAtTensor03 (T + T') x := mdifferentiableAt_add_section hT hT'
    apply ContinuousLinearMap.ext; intro v
    apply ContinuousLinearMap.ext; intro y
    apply ContinuousLinearMap.ext; intro z
    apply ContinuousLinearMap.ext; intro w
    set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    set Z : Π x : M, TangentSpace I x := FiberBundle.extend E z
    set W : Π x : M, TangentSpace I x := FiberBundle.extend E w
    have hX : MDiffAt (T% X) x := mdifferentiableAt_extend ..
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
    have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend ..
    have hW : MDiffAt (T% W) x := mdifferentiableAt_extend ..
    have hXx : X x = v := by simp [X]
    have hYx : Y x = y := by simp [Y]
    have hZx : Z x = z := by simp [Z]
    have hWx : W x = w := by simp [W]
    change tensor03CovFun cov (T + T') x v y z w =
      ((tensor03CovFun cov T x) + (tensor03CovFun cov T' x)) v y z w
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
    change tensor03CovFun cov (T + T') x v y z w =
      tensor03CovFun cov T x v y z w + tensor03CovFun cov T' x v y z w
    rw [show v = X x from hXx.symm, show y = Y x from hYx.symm,
        show z = Z x from hZx.symm, show w = W x from hWx.symm]
    rw [tensor03CovFun_apply, tensor03CovFun_apply, tensor03CovFun_apply]
    rw [tensor03CovAt_apply_of_diff_extend cov hsum_T hX hY hZ hW,
        tensor03CovAt_apply_of_diff_extend cov hT_t hX hY hZ hW,
        tensor03CovAt_apply_of_diff_extend cov hT'_t hX hY hZ hW]
    change extDerivFun (I := I) (fun b => (T + T') b (Y b) (Z b) (W b)) x (X x)
        - (T + T') x (cov.toFun Y x (X x)) (Z x) (W x)
        - (T + T') x (Y x) (cov.toFun Z x (X x)) (W x)
        - (T + T') x (Y x) (Z x) (cov.toFun W x (X x)) =
      (extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x))) +
      (extDerivFun (I := I) (fun b => T' b (Y b) (Z b) (W b)) x (X x)
        - T' x (cov.toFun Y x (X x)) (Z x) (W x)
        - T' x (Y x) (cov.toFun Z x (X x)) (W x)
        - T' x (Y x) (Z x) (cov.toFun W x (X x)))
    have hpair_T : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT_t hY hZ hW
    have hpair_T' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T' b (Y b) (Z b) (W b)) x :=
      mdifferentiableAt_tensor03_pairing hT'_t hY hZ hW
    have hpair_eq : (fun b : M => (T + T') b (Y b) (Z b) (W b)) =
        (fun b : M => T b (Y b) (Z b) (W b)) + (fun b : M => T' b (Y b) (Z b) (W b)) := by
      funext b
      change (T + T') b (Y b) (Z b) (W b) = T b (Y b) (Z b) (W b) + T' b (Y b) (Z b) (W b)
      have : (T + T') b = T b + T' b := rfl
      rw [this, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.add_apply]
    have hext_add : extDerivFun (I := I) (fun b => (T + T') b (Y b) (Z b) (W b)) x =
        extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x +
        extDerivFun (I := I) (fun b => T' b (Y b) (Z b) (W b)) x := by
      rw [hpair_eq, extDerivFun_add hpair_T hpair_T']
    rw [hext_add, ContinuousLinearMap.add_apply]
    have e1 : (T + T') x (cov.toFun Y x (X x)) (Z x) (W x) =
        T x (cov.toFun Y x (X x)) (Z x) (W x) + T' x (cov.toFun Y x (X x)) (Z x) (W x) := by
      have : (T + T') x = T x + T' x := rfl
      rw [this, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.add_apply]
    have e2 : (T + T') x (Y x) (cov.toFun Z x (X x)) (W x) =
        T x (Y x) (cov.toFun Z x (X x)) (W x) + T' x (Y x) (cov.toFun Z x (X x)) (W x) := by
      have : (T + T') x = T x + T' x := rfl
      rw [this, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.add_apply]
    have e3 : (T + T') x (Y x) (Z x) (cov.toFun W x (X x)) =
        T x (Y x) (Z x) (cov.toFun W x (X x)) + T' x (Y x) (Z x) (cov.toFun W x (X x)) := by
      have : (T + T') x = T x + T' x := rfl
      rw [this, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.add_apply]
    rw [e1, e2, e3]
    ring
  leibniz {T g x} hT hg _hx := by
    classical
    have hT_t : MDiffAtTensor03 T x := hT
    have hsum_T : MDiffAtTensor03 (g • T) x := hg.smul_section hT
    apply ContinuousLinearMap.ext; intro v
    apply ContinuousLinearMap.ext; intro y
    apply ContinuousLinearMap.ext; intro z
    apply ContinuousLinearMap.ext; intro w
    set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    set Z : Π x : M, TangentSpace I x := FiberBundle.extend E z
    set W : Π x : M, TangentSpace I x := FiberBundle.extend E w
    have hX : MDiffAt (T% X) x := mdifferentiableAt_extend ..
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
    have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend ..
    have hW : MDiffAt (T% W) x := mdifferentiableAt_extend ..
    have hXx : X x = v := by simp [X]
    have hYx : Y x = y := by simp [Y]
    have hZx : Z x = z := by simp [Z]
    have hWx : W x = w := by simp [W]
    rw [show v = X x from hXx.symm, show y = Y x from hYx.symm,
        show z = Z x from hZx.symm, show w = W x from hWx.symm]
    rw [tensor03CovFun_apply, tensor03CovFun_apply]
    rw [tensor03CovAt_apply_of_diff_extend cov hsum_T hX hY hZ hW]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply]
    rw [tensor03CovAt_apply_of_diff_extend cov hT_t hX hY hZ hW]
    change extDerivFun (I := I) (fun b => (g • T) b (Y b) (Z b) (W b)) x (X x)
        - (g • T) x (cov.toFun Y x (X x)) (Z x) (W x)
        - (g • T) x (Y x) (cov.toFun Z x (X x)) (W x)
        - (g • T) x (Y x) (Z x) (cov.toFun W x (X x)) =
      g x • (extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x) (W x)
        - T x (Y x) (cov.toFun Z x (X x)) (W x)
        - T x (Y x) (Z x) (cov.toFun W x (X x))) +
      extDerivFun (I := I) g x (X x) • T x (Y x) (Z x) (W x)
    set h : M → ℝ := fun b => T b (Y b) (Z b) (W b) with hh_def
    have hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x :=
      mdifferentiableAt_tensor03_pairing hT_t hY hZ hW
    have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g x := hg
    have hpair_eq : (fun b : M => (g • T) b (Y b) (Z b) (W b)) = (fun b : M => g b * h b) := by
      funext b
      change (g • T) b (Y b) (Z b) (W b) = g b * h b
      have : (g • T) b = g b • T b := rfl
      rw [this, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hpair_eq, extDerivFun_mul_apply hg' hh]
    have s1 : (g • T) x (cov.toFun Y x (X x)) (Z x) (W x) =
        g x • T x (cov.toFun Y x (X x)) (Z x) (W x) := by
      have : (g • T) x = g x • T x := rfl
      rw [this, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply]
    have s2 : (g • T) x (Y x) (cov.toFun Z x (X x)) (W x) =
        g x • T x (Y x) (cov.toFun Z x (X x)) (W x) := by
      have : (g • T) x = g x • T x := rfl
      rw [this, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply]
    have s3 : (g • T) x (Y x) (Z x) (cov.toFun W x (X x)) =
        g x • T x (Y x) (Z x) (cov.toFun W x (X x)) := by
      have : (g • T) x = g x • T x := rfl
      rw [this, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply]
    rw [s1, s2, s3]
    have hhx : h x = T x (Y x) (Z x) (W x) := rfl
    rw [hhx]
    simp only [smul_eq_mul]
    ring

def tensor03Cov
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    CovariantDerivative I (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M =>
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) where
  toFun := tensor03CovFun cov
  isCovariantDerivativeOnUniv := tensor03CovFun_isCovariantDerivativeOn cov

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma tensor03Cov_toFun
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    (tensor03Cov cov).toFun = tensor03CovFun cov := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem tensor03Cov_pairing
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x)
    {Y Z W : Π x : M, TangentSpace I x}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) (hW : MDiffAt (T% W) x)
    (v : TangentSpace I x) :
    extDerivFun (I := I) (fun b => T b (Y b) (Z b) (W b)) x v =
      ((tensor03Cov cov).toFun T x v) (Y x) (Z x) (W x)
        + T x (cov.toFun Y x v) (Z x) (W x)
        + T x (Y x) (cov.toFun Z x v) (W x)
        + T x (Y x) (Z x) (cov.toFun W x v) := by
  classical
  set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
  have hX : MDiffAt (T% X) x := mdifferentiableAt_extend ..
  have hXx : X x = v := by simp [X]
  rw [show v = X x from hXx.symm]
  rw [tensor03Cov_toFun, tensor03CovFun_apply,
      tensor03CovAt_apply_of_diff_extend cov hT hX hY hZ hW]
  unfold tensor03Scalar
  ring

def tensor02CovIterate
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) →
      (Π x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  fun T => (tensor03Cov cov).toFun ((tensor02Cov cov).toFun T)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensor02CovIterate_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M) :
    tensor02CovIterate cov T x =
      (tensor03Cov cov).toFun ((tensor02Cov cov).toFun T) x := rfl

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem tensor03Cov_add
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T T' : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (hT' : MDiffAtTensor03 T' x) :
    (tensor03Cov cov).toFun (T + T') x =
      (tensor03Cov cov).toFun T x + (tensor03Cov cov).toFun T' x := by
  set D := tensor03Cov cov
  exact D.isCovariantDerivativeOnUniv.add hT hT' (Set.mem_univ x)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem tensor03Cov_smul
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (a : ℝ) (hT : MDiffAtTensor03 T x) :
    (tensor03Cov cov).toFun (a • T) x = a • (tensor03Cov cov).toFun T x := by
  set D := tensor03Cov cov
  exact D.isCovariantDerivativeOnUniv.smul_const a hT (Set.mem_univ x)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem tensor03Cov_sub
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T T' : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {x : M} (hT : MDiffAtTensor03 T x) (hT' : MDiffAtTensor03 T' x) :
    (tensor03Cov cov).toFun (T - T') x =
      (tensor03Cov cov).toFun T x - (tensor03Cov cov).toFun T' x := by
  classical
  set D := tensor03Cov cov with hD_def
  have hcovOn := D.isCovariantDerivativeOnUniv
  have hT'neg : MDiffAtTensor03 (-T') x := mdifferentiableAt_neg_section hT'
  have hneg : D.toFun (-T') x = - D.toFun T' x := by
    have hsum : D.toFun (T' + (-T')) x = D.toFun T' x + D.toFun (-T') x :=
      hcovOn.add hT' hT'neg (Set.mem_univ x)
    rw [add_neg_cancel] at hsum
    rw [hcovOn.zero (Set.mem_univ x)] at hsum
    exact eq_neg_of_add_eq_zero_right hsum.symm
  have hadd : D.toFun (T + (-T')) x = D.toFun T x + D.toFun (-T') x :=
    hcovOn.add hT hT'neg (Set.mem_univ x)
  have hTsub : (T - T' : Π x : M,
      TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) =
      T + (-T') := sub_eq_add_neg T T'
  rw [hTsub, hadd, hneg, ← sub_eq_add_neg]

section NormBridge

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

def biForm₂ToModel :
    (F →L[ℝ] F →L[ℝ] ℝ) ≃ₗ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 2 => F) ℝ :=
  ((ContinuousLinearEquiv.refl ℝ F).arrowCongr
      (continuousMultilinearCurryFin1 ℝ F ℝ).symm.toContinuousLinearEquiv).toLinearEquiv.trans
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => F) ℝ).symm.toLinearEquiv

theorem biForm₂ToModel_apply (B : F →L[ℝ] F →L[ℝ] ℝ) (v : Fin 2 → F) :
    biForm₂ToModel F B v = B (v 0) (v 1) := by
  classical
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => F) ℝ).symm
      (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
          (continuousMultilinearCurryFin1 ℝ F ℝ).symm.toContinuousLinearEquiv) B) v =
    B (v 0) (v 1)
  rw [continuousMultilinearCurryLeftEquiv_symm_apply,
    ContinuousLinearEquiv.arrowCongr_apply]
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [continuousMultilinearCurryFin1_symm_apply]
  rfl

theorem biForm₂ToModel_norm_map (B : F →L[ℝ] F →L[ℝ] ℝ) :
    ‖biForm₂ToModel F B‖ = ‖B‖ := by
  classical
  refine le_antisymm ?_ ?_
  · refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg B) (fun m => ?_)
    rw [biForm₂ToModel_apply, Fin.prod_univ_two]
    calc ‖B (m 0) (m 1)‖
        ≤ ‖B‖ * ‖m 0‖ * ‖m 1‖ := B.le_opNorm₂ (m 0) (m 1)
      _ = ‖B‖ * (‖m 0‖ * ‖m 1‖) := by ring
  · refine ContinuousLinearMap.opNorm_le_bound₂ B (norm_nonneg _) (fun v w => ?_)
    have hsymm : B v w = biForm₂ToModel F B ![v, w] := by
      rw [biForm₂ToModel_apply]; simp
    rw [hsymm]
    calc ‖biForm₂ToModel F B ![v, w]‖
        ≤ ‖biForm₂ToModel F B‖ * ∏ i : Fin 2, ‖(![v, w] : Fin 2 → F) i‖ :=
          (biForm₂ToModel F B).le_opNorm _
      _ = ‖biForm₂ToModel F B‖ * ‖v‖ * ‖w‖ := by
          rw [Fin.prod_univ_two]; simp [Matrix.cons_val_zero, Matrix.cons_val_one]; ring

def biForm₂ToModelₗᵢ :
    (F →L[ℝ] F →L[ℝ] ℝ) ≃ₗᵢ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 2 => F) ℝ :=
  { biForm₂ToModel F with norm_map' := biForm₂ToModel_norm_map F }

def triFormToModel :
    (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) ≃ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 3 => F) ℝ :=
  ((ContinuousLinearEquiv.refl ℝ F).arrowCongr
      (biForm₂ToModelₗᵢ F).toContinuousLinearEquiv).toLinearEquiv.trans
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm.toLinearEquiv

theorem triFormToModel_apply (B : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) (v : Fin 3 → F) :
    triFormToModel F B v = B (v 0) (v 1) (v 2) := by
  classical
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm
      (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
          (biForm₂ToModelₗᵢ F).toContinuousLinearEquiv) B) v =
    B (v 0) (v 1) (v 2)
  rw [continuousMultilinearCurryLeftEquiv_symm_apply,
    ContinuousLinearEquiv.arrowCongr_apply]
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  change (biForm₂ToModelₗᵢ F) (B (v 0)) (Fin.tail v) = _
  rw [show ⇑(biForm₂ToModelₗᵢ F) = ⇑(biForm₂ToModel F) from rfl, biForm₂ToModel_apply]
  rfl

theorem triFormToModel_norm_map (B : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :
    ‖triFormToModel F B‖ = ‖B‖ := by
  classical
  have h_curry : ‖triFormToModel F B‖ =
      ‖((ContinuousLinearEquiv.refl ℝ F).arrowCongr
          (biForm₂ToModelₗᵢ F).toContinuousLinearEquiv) B‖ := by
    change ‖(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm
      (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
        (biForm₂ToModelₗᵢ F).toContinuousLinearEquiv) B)‖ = _
    rw [(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => F) ℝ).symm.norm_map]
  rw [h_curry]
  have hcomp : ((ContinuousLinearEquiv.refl ℝ F).arrowCongr
        (biForm₂ToModelₗᵢ F).toContinuousLinearEquiv) B =
      (biForm₂ToModelₗᵢ F).toLinearIsometry.toContinuousLinearMap.comp B := by
    ext u
    simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.refl_symm,
      ContinuousLinearEquiv.refl_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearMap.coe_comp', Function.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
  rw [hcomp, (biForm₂ToModelₗᵢ F).toLinearIsometry.norm_toContinuousLinearMap_comp]

def triFormToModelₗᵢ :
    (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) ≃ₗᵢ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 3 => F) ℝ :=
  { triFormToModel F with norm_map' := triFormToModel_norm_map F }

def quadFormToModel :
    (F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) ≃ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ :=
  ((ContinuousLinearEquiv.refl ℝ F).arrowCongr
      (triFormToModelₗᵢ F).toContinuousLinearEquiv).toLinearEquiv.trans
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => F) ℝ).symm.toLinearEquiv

theorem quadFormToModel_apply (B : F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) (v : Fin 4 → F) :
    quadFormToModel F B v = B (v 0) (v 1) (v 2) (v 3) := by
  classical
  change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => F) ℝ).symm
      (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
          (triFormToModelₗᵢ F).toContinuousLinearEquiv) B) v =
    B (v 0) (v 1) (v 2) (v 3)
  rw [continuousMultilinearCurryLeftEquiv_symm_apply,
    ContinuousLinearEquiv.arrowCongr_apply]
  simp only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  change (triFormToModelₗᵢ F) (B (v 0)) (Fin.tail v) = _
  rw [show ⇑(triFormToModelₗᵢ F) = ⇑(triFormToModel F) from rfl, triFormToModel_apply]
  rfl

theorem quadFormToModel_norm_map (B : F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) :
    ‖quadFormToModel F B‖ = ‖B‖ := by
  classical
  have h_curry : ‖quadFormToModel F B‖ =
      ‖((ContinuousLinearEquiv.refl ℝ F).arrowCongr
          (triFormToModelₗᵢ F).toContinuousLinearEquiv) B‖ := by
    change ‖(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => F) ℝ).symm
      (((ContinuousLinearEquiv.refl ℝ F).arrowCongr
        (triFormToModelₗᵢ F).toContinuousLinearEquiv) B)‖ = _
    rw [(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 4 => F) ℝ).symm.norm_map]
  rw [h_curry]
  have hcomp : ((ContinuousLinearEquiv.refl ℝ F).arrowCongr
        (triFormToModelₗᵢ F).toContinuousLinearEquiv) B =
      (triFormToModelₗᵢ F).toLinearIsometry.toContinuousLinearMap.comp B := by
    ext u
    simp only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.refl_symm,
      ContinuousLinearEquiv.refl_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearMap.coe_comp', Function.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
  rw [hcomp, (triFormToModelₗᵢ F).toLinearIsometry.norm_toContinuousLinearMap_comp]

def quadFormToModelₗᵢ :
    (F →L[ℝ] F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) ≃ₗᵢ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin 4 => F) ℝ :=
  { quadFormToModel F with norm_map' := quadFormToModel_norm_map F }

end NormBridge

end Connection
end Integral
end DifferentialGeometry

end
