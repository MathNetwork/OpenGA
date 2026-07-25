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


noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

local instance tensor02FiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  inferInstance

local instance tensor02VectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  inferInstance

local instance tensor02ContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) I :=
  inferInstance

def MDiffAtTensor02
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
    (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (T b)) x

def tensor02Scalar
    (cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M)
    (X Y Z : Π x : M, TangentSpace I x) : ℝ :=
  extDerivFun (I := I) (fun b => T b (Y b) (Z b)) x (X x)
    - T x (cov Y x (X x)) (Z x)
    - T x (Y x) (cov Z x (X x))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
lemma tensor02Scalar_def
    (cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M)
    (X Y Z : Π x : M, TangentSpace I x) :
    tensor02Scalar cov T x X Y Z =
      extDerivFun (I := I) (fun b => T b (Y b) (Z b)) x (X x)
        - T x (cov Y x (X x)) (Z x)
        - T x (Y x) (cov Z x (X x)) := rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma mdifferentiableAt_tensor02_apply_one
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {Y : Π x : M, TangentSpace I x} {x : M}
    (hT : MDiffAtTensor02 T x) (hY : MDiffAt (T% Y) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (T b (Y b))) x := by
  exact MDifferentiableAt.clm_bundle_apply
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (b := fun b : M => b)
    (ϕ := fun b => T b) (v := fun b => Y b) hT hY

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma mdifferentiableAt_tensor02_pairing
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hT : MDiffAtTensor02 T x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b)) x := by
  have h1 := mdifferentiableAt_tensor02_apply_one hT hY
  have h2 : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun m => TotalSpace.mk' ℝ (E := fun _ : M => ℝ) m (T m (Y m) (Z m))) x :=
    MDifferentiableAt.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun _ : M => ℝ)
      (b := fun b : M => b)
      (ϕ := fun b => T b (Y b)) (v := fun b => Z b) h1 hZ
  rw [mdifferentiableAt_totalSpace] at h2
  exact h2.2

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma tensor02Scalar_tensorialAt_X
    (_covOn : IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (cov : (Π x : M, TangentSpace I x) →
        (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
      Set.univ)
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (x : M) (Y Z : Π x : M, TangentSpace I x)
    (_hY : MDiffAt (T% Y) x) (_hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (tensor02Scalar cov T x · Y Z) x where
  smul {f X} _hf _hX := by
    classical
    unfold tensor02Scalar
    have hfX : (f • X) x = f x • X x := rfl
    rw [hfX]
    rw [(extDerivFun (I := I) (fun b => T b (Y b) (Z b)) x).map_smul]
    rw [(cov.toFun Y x).map_smul, (cov.toFun Z x).map_smul]
    rw [(T x).map_smul, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul]
    rw [smul_sub, smul_sub]
  add {X X'} _hX _hX' := by
    classical
    unfold tensor02Scalar
    have hXX' : (X + X') x = X x + X' x := rfl
    rw [hXX']
    rw [map_add, (cov.toFun Y x).map_add, (cov.toFun Z x).map_add]
    rw [(T x).map_add, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.map_add]
    abel

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma tensor02Scalar_tensorialAt_Y
    (covOn : IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (cov : (Π x : M, TangentSpace I x) →
        (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
      Set.univ)
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hT : MDiffAtTensor02 T x)
    (X : Π x : M, TangentSpace I x) (_hX : MDiffAt (T% X) x)
    (Z : Π x : M, TangentSpace I x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (tensor02Scalar cov T x X · Z) x where
  smul {g Y} hg hY := by
    classical
    set h : M → ℝ := fun b => T b (Y b) (Z b) with hh_def
    have hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x :=
      mdifferentiableAt_tensor02_pairing hT hY hZ
    have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g x := hg
    have hfun : (fun b : M => T b ((g • Y) b) (Z b)) = (fun b : M => g b * h b) := by
      funext b
      change T b ((g • Y) b) (Z b) = g b * h b
      have : (g • Y) b = g b • Y b := rfl
      rw [this, ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    change extDerivFun (I := I) (fun b => T b ((g • Y) b) (Z b)) x (X x)
        - T x (cov.toFun (g • Y) x (X x)) (Z x)
        - T x ((g • Y) x) (cov.toFun Z x (X x)) =
      g x • (extDerivFun (I := I) h x (X x)
        - T x (cov.toFun Y x (X x)) (Z x)
        - T x (Y x) (cov.toFun Z x (X x)))
    rw [hfun, extDerivFun_mul_apply hg' hh, covOn.leibniz hY hg (Set.mem_univ x)]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
    rw [ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply]
    have h_gY_x : (g • Y) x = g x • Y x := rfl
    rw [h_gY_x, ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply]
    have hhx : h x = T x (Y x) (Z x) := rfl
    rw [hhx]
    simp only [smul_eq_mul]
    ring
  add {Y Y'} hY hY' := by
    classical
    change extDerivFun (I := I) (fun b => T b ((Y + Y') b) (Z b)) x (X x)
        - T x (cov.toFun (Y + Y') x (X x)) (Z x)
        - T x ((Y + Y') x) (cov.toFun Z x (X x)) =
      (extDerivFun (I := I) (fun b => T b (Y b) (Z b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x)
        - T x (Y x) (cov.toFun Z x (X x))) +
      (extDerivFun (I := I) (fun b => T b (Y' b) (Z b)) x (X x)
        - T x (cov.toFun Y' x (X x)) (Z x)
        - T x (Y' x) (cov.toFun Z x (X x)))
    have hadd_fun : (fun b : M => T b ((Y + Y') b) (Z b)) =
        (fun b : M => T b (Y b) (Z b)) + (fun b : M => T b (Y' b) (Z b)) := by
      funext b
      change T b ((Y + Y') b) (Z b) = T b (Y b) (Z b) + T b (Y' b) (Z b)
      have : (Y + Y') b = Y b + Y' b := rfl
      rw [this, ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply]
    have h1 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b)) x :=
      mdifferentiableAt_tensor02_pairing hT hY hZ
    have h2 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y' b) (Z b)) x :=
      mdifferentiableAt_tensor02_pairing hT hY' hZ
    have hext_add : extDerivFun (I := I) (fun b => T b ((Y + Y') b) (Z b)) x =
        extDerivFun (I := I) (fun b => T b (Y b) (Z b)) x +
        extDerivFun (I := I) (fun b => T b (Y' b) (Z b)) x := by
      rw [hadd_fun, extDerivFun_add h1 h2]
    rw [hext_add, ContinuousLinearMap.add_apply]
    rw [covOn.add hY hY' (Set.mem_univ x), ContinuousLinearMap.add_apply,
        ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply]
    have h_YY' : (Y + Y') x = Y x + Y' x := rfl
    rw [h_YY', ContinuousLinearMap.map_add, ContinuousLinearMap.add_apply]
    abel

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma tensor02Scalar_tensorialAt_Z
    (covOn : IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (cov : (Π x : M, TangentSpace I x) →
        (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
      Set.univ)
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hT : MDiffAtTensor02 T x)
    (X : Π x : M, TangentSpace I x) (_hX : MDiffAt (T% X) x)
    (Y : Π x : M, TangentSpace I x) (hY : MDiffAt (T% Y) x) :
    TensorialAt I E (tensor02Scalar cov T x X Y ·) x where
  smul {g Z} hg hZ := by
    classical
    set h : M → ℝ := fun b => T b (Y b) (Z b) with hh_def
    have hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x :=
      mdifferentiableAt_tensor02_pairing hT hY hZ
    have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g x := hg
    have hfun : (fun b : M => T b (Y b) ((g • Z) b)) = (fun b : M => g b * h b) := by
      funext b
      change T b (Y b) ((g • Z) b) = g b * h b
      have : (g • Z) b = g b • Z b := rfl
      rw [this, ContinuousLinearMap.map_smul, smul_eq_mul]
    change extDerivFun (I := I) (fun b => T b (Y b) ((g • Z) b)) x (X x)
        - T x (cov.toFun Y x (X x)) ((g • Z) x)
        - T x (Y x) (cov.toFun (g • Z) x (X x)) =
      g x • (extDerivFun (I := I) h x (X x)
        - T x (cov.toFun Y x (X x)) (Z x)
        - T x (Y x) (cov.toFun Z x (X x)))
    rw [hfun, extDerivFun_mul_apply hg' hh, covOn.leibniz hZ hg (Set.mem_univ x)]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
    have h_gZ_x : (g • Z) x = g x • Z x := rfl
    rw [h_gZ_x]
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.map_add,
        ContinuousLinearMap.map_smul, (T x (Y x)).map_smul]
    have hhx : h x = T x (Y x) (Z x) := rfl
    rw [hhx]
    simp only [smul_eq_mul]
    ring
  add {Z Z'} hZ hZ' := by
    classical
    change extDerivFun (I := I) (fun b => T b (Y b) ((Z + Z') b)) x (X x)
        - T x (cov.toFun Y x (X x)) ((Z + Z') x)
        - T x (Y x) (cov.toFun (Z + Z') x (X x)) =
      (extDerivFun (I := I) (fun b => T b (Y b) (Z b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x)
        - T x (Y x) (cov.toFun Z x (X x))) +
      (extDerivFun (I := I) (fun b => T b (Y b) (Z' b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z' x)
        - T x (Y x) (cov.toFun Z' x (X x)))
    have hadd_fun : (fun b : M => T b (Y b) ((Z + Z') b)) =
        (fun b : M => T b (Y b) (Z b)) + (fun b : M => T b (Y b) (Z' b)) := by
      funext b
      change T b (Y b) ((Z + Z') b) = T b (Y b) (Z b) + T b (Y b) (Z' b)
      have : (Z + Z') b = Z b + Z' b := rfl
      rw [this, ContinuousLinearMap.map_add]
    have h1 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b)) x :=
      mdifferentiableAt_tensor02_pairing hT hY hZ
    have h2 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z' b)) x :=
      mdifferentiableAt_tensor02_pairing hT hY hZ'
    have hext_add : extDerivFun (I := I) (fun b => T b (Y b) ((Z + Z') b)) x =
        extDerivFun (I := I) (fun b => T b (Y b) (Z b)) x +
        extDerivFun (I := I) (fun b => T b (Y b) (Z' b)) x := by
      rw [hadd_fun, extDerivFun_add h1 h2]
    rw [hext_add, ContinuousLinearMap.add_apply]
    rw [covOn.add hZ hZ' (Set.mem_univ x), ContinuousLinearMap.add_apply,
        ContinuousLinearMap.map_add]
    have h_ZZ' : (Z + Z') x = Z x + Z' x := rfl
    rw [h_ZZ', ContinuousLinearMap.map_add]
    abel

private noncomputable def tensor02BilinAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hT : MDiffAtTensor02 T x) (v : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  let X : Π x : M, TangentSpace I x := FiberBundle.extend E v
  TensorialAt.mkHom₂
    (Φ := fun Y Z => tensor02Scalar (cov.toFun) T x X Y Z)
    x
    (fun Z hZ =>
      tensor02Scalar_tensorialAt_Y cov.isCovariantDerivativeOnUniv hT
        X (mdifferentiableAt_extend ..) Z hZ)
    (fun Y hY =>
      tensor02Scalar_tensorialAt_Z cov.isCovariantDerivativeOnUniv hT
        X (mdifferentiableAt_extend ..) Y hY)

omit [NeZero (Module.finrank ℝ E)] in
private lemma tensor02BilinAt_apply_extend
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hT : MDiffAtTensor02 T x) (v : TangentSpace I x)
    {Y Z : Π x : M, TangentSpace I x}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    tensor02BilinAt cov hT v (Y x) (Z x) =
      tensor02Scalar (cov.toFun) T x (FiberBundle.extend E v) Y Z := by
  classical
  unfold tensor02BilinAt
  exact TensorialAt.mkHom₂_apply _ _ hY hZ

private noncomputable def tensor02XSlot
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hT : MDiffAtTensor02 T x) :
    TangentSpace I x →ₗ[ℝ]
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) where
  toFun v := tensor02BilinAt cov hT v
  map_add' v v' := by
    classical
    ext y z
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    set Z : Π x : M, TangentSpace I x := FiberBundle.extend E z
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
    have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend ..
    have hYx : Y x = y := FiberBundle.extend_apply_self E y
    have hZx : Z x = z := FiberBundle.extend_apply_self E z
    rw [show y = Y x from hYx.symm, show z = Z x from hZx.symm]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
    rw [tensor02BilinAt_apply_extend cov hT (v + v') hY hZ,
        tensor02BilinAt_apply_extend cov hT v hY hZ,
        tensor02BilinAt_apply_extend cov hT v' hY hZ]
    have h1 : (FiberBundle.extend E (v + v') : Π x : M, TangentSpace I x) x = v + v' :=
      FiberBundle.extend_apply_self E (v + v')
    have h2 : (FiberBundle.extend E v : Π x : M, TangentSpace I x) x = v :=
      FiberBundle.extend_apply_self E v
    have h3 : (FiberBundle.extend E v' : Π x : M, TangentSpace I x) x = v' :=
      FiberBundle.extend_apply_self E v'
    unfold tensor02Scalar
    rw [h1, h2, h3]
    rw [(extDerivFun (I := I) (fun b => T b (Y b) (Z b)) x).map_add]
    rw [(cov.toFun Y x).map_add, (cov.toFun Z x).map_add]
    rw [(T x).map_add, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.map_add]
    abel
  map_smul' c v := by
    classical
    ext y z
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    set Z : Π x : M, TangentSpace I x := FiberBundle.extend E z
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
    have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend ..
    have hYx : Y x = y := FiberBundle.extend_apply_self E y
    have hZx : Z x = z := FiberBundle.extend_apply_self E z
    rw [show y = Y x from hYx.symm, show z = Z x from hZx.symm]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    rw [tensor02BilinAt_apply_extend cov hT (c • v) hY hZ,
        tensor02BilinAt_apply_extend cov hT v hY hZ]
    have h1 : (FiberBundle.extend E (c • v) : Π x : M, TangentSpace I x) x = c • v :=
      FiberBundle.extend_apply_self E (c • v)
    have h2 : (FiberBundle.extend E v : Π x : M, TangentSpace I x) x = v :=
      FiberBundle.extend_apply_self E v
    unfold tensor02Scalar
    rw [h1, h2]
    rw [(extDerivFun (I := I) (fun b => T b (Y b) (Z b)) x).map_smul]
    rw [(cov.toFun Y x).map_smul, (cov.toFun Z x).map_smul]
    rw [(T x).map_smul, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.map_smul]
    simp only [smul_eq_mul, RingHom.id_apply]
    ring

def tensor02CovAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) := by
  classical
  by_cases hT : MDiffAtTensor02 T x
  · exact LinearMap.toContinuousLinearMap (tensor02XSlot cov hT)
  · exact 0

omit [NeZero (Module.finrank ℝ E)] in
lemma tensor02CovAt_apply_of_diff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hT : MDiffAtTensor02 T x) (v : TangentSpace I x) :
    tensor02CovAt cov T x v = tensor02BilinAt cov hT v := by
  classical
  unfold tensor02CovAt
  rw [dif_pos hT]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma tensor02CovAt_apply_of_diff_extend
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hT : MDiffAtTensor02 T x) {X Y Z : Π x : M, TangentSpace I x}
    (_hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    tensor02CovAt cov T x (X x) (Y x) (Z x) =
      tensor02Scalar (cov.toFun) T x X Y Z := by
  classical
  rw [tensor02CovAt_apply_of_diff cov hT (X x)]
  rw [tensor02BilinAt_apply_extend cov hT (X x) hY hZ]
  unfold tensor02Scalar
  have hext : (FiberBundle.extend E (X x) : Π x : M, TangentSpace I x) x = X x :=
    FiberBundle.extend_apply_self E (X x)
  rw [hext]

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensor02CovAt_of_not_diff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hT : ¬ MDiffAtTensor02 T x) :
    tensor02CovAt cov T x = 0 := by
  classical
  unfold tensor02CovAt
  rw [dif_neg hT]

def tensor02CovFun
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) →
      (Π x : M, TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)) :=
  fun T x => tensor02CovAt cov T x

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensor02CovFun_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M) :
    tensor02CovFun cov T x = tensor02CovAt cov T x := rfl

set_option maxHeartbeats 800000 in

omit [NeZero (Module.finrank ℝ E)] in
lemma tensor02CovFun_isCovariantDerivativeOn
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    IsCovariantDerivativeOn (V := (fun x : M =>
        TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))
      (E →L[ℝ] E →L[ℝ] ℝ)
      (tensor02CovFun cov) Set.univ where
  add {T T'} {x} hT hT' _hx := by
    classical
    have hT_t : MDiffAtTensor02 T x := hT
    have hT'_t : MDiffAtTensor02 T' x := hT'
    have hsum_T : MDiffAtTensor02 (T + T') x :=
      mdifferentiableAt_add_section hT hT'
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro y
    apply ContinuousLinearMap.ext
    intro z
    set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    set Z : Π x : M, TangentSpace I x := FiberBundle.extend E z
    have hX : MDiffAt (T% X) x := mdifferentiableAt_extend ..
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
    have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend ..
    have hXx : X x = v := by simp [X]
    have hYx : Y x = y := by simp [Y]
    have hZx : Z x = z := by simp [Z]
    change tensor02CovFun cov (T + T') x v y z =
      ((tensor02CovFun cov T x) + (tensor02CovFun cov T' x)) v y z
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.add_apply]
    change tensor02CovFun cov (T + T') x v y z =
      tensor02CovFun cov T x v y z + tensor02CovFun cov T' x v y z
    rw [show v = X x from hXx.symm, show y = Y x from hYx.symm,
        show z = Z x from hZx.symm]
    rw [tensor02CovFun_apply, tensor02CovFun_apply, tensor02CovFun_apply]
    rw [tensor02CovAt_apply_of_diff_extend cov hsum_T hX hY hZ,
        tensor02CovAt_apply_of_diff_extend cov hT_t hX hY hZ,
        tensor02CovAt_apply_of_diff_extend cov hT'_t hX hY hZ]
    change extDerivFun (I := I) (fun b => (T + T') b (Y b) (Z b)) x (X x)
        - (T + T') x (cov.toFun Y x (X x)) (Z x)
        - (T + T') x (Y x) (cov.toFun Z x (X x)) =
      (extDerivFun (I := I) (fun b => T b (Y b) (Z b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x)
        - T x (Y x) (cov.toFun Z x (X x))) +
      (extDerivFun (I := I) (fun b => T' b (Y b) (Z b)) x (X x)
        - T' x (cov.toFun Y x (X x)) (Z x)
        - T' x (Y x) (cov.toFun Z x (X x)))
    have hpair_T : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T b (Y b) (Z b)) x :=
      mdifferentiableAt_tensor02_pairing hT_t hY hZ
    have hpair_T' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => T' b (Y b) (Z b)) x :=
      mdifferentiableAt_tensor02_pairing hT'_t hY hZ
    have hpair_eq : (fun b : M => (T + T') b (Y b) (Z b)) =
        (fun b : M => T b (Y b) (Z b)) + (fun b : M => T' b (Y b) (Z b)) := by
      funext b
      change (T + T') b (Y b) (Z b) = T b (Y b) (Z b) + T' b (Y b) (Z b)
      have : (T + T') b = T b + T' b := rfl
      rw [this, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
    have hext_add : extDerivFun (I := I) (fun b => (T + T') b (Y b) (Z b)) x =
        extDerivFun (I := I) (fun b => T b (Y b) (Z b)) x +
        extDerivFun (I := I) (fun b => T' b (Y b) (Z b)) x := by
      rw [hpair_eq, extDerivFun_add hpair_T hpair_T']
    rw [hext_add, ContinuousLinearMap.add_apply]
    have h_add_one : (T + T') x (cov.toFun Y x (X x)) =
        T x (cov.toFun Y x (X x)) + T' x (cov.toFun Y x (X x)) := by
      have : (T + T') x = T x + T' x := rfl
      rw [this, ContinuousLinearMap.add_apply]
    have h_add_two : (T + T') x (Y x) =
        T x (Y x) + T' x (Y x) := by
      have : (T + T') x = T x + T' x := rfl
      rw [this, ContinuousLinearMap.add_apply]
    rw [h_add_one, h_add_two]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
    ring
  leibniz {T g x} hT hg _hx := by
    classical
    have hT_t : MDiffAtTensor02 T x := hT
    have hsum_T : MDiffAtTensor02 (g • T) x := hg.smul_section hT
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro y
    apply ContinuousLinearMap.ext
    intro z
    set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    set Z : Π x : M, TangentSpace I x := FiberBundle.extend E z
    have hX : MDiffAt (T% X) x := mdifferentiableAt_extend ..
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
    have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend ..
    have hXx : X x = v := by simp [X]
    have hYx : Y x = y := by simp [Y]
    have hZx : Z x = z := by simp [Z]
    rw [show v = X x from hXx.symm, show y = Y x from hYx.symm,
        show z = Z x from hZx.symm]
    rw [tensor02CovFun_apply, tensor02CovFun_apply]
    rw [tensor02CovAt_apply_of_diff_extend cov hsum_T hX hY hZ]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply]
    rw [tensor02CovAt_apply_of_diff_extend cov hT_t hX hY hZ]
    change extDerivFun (I := I) (fun b => (g • T) b (Y b) (Z b)) x (X x)
        - (g • T) x (cov.toFun Y x (X x)) (Z x)
        - (g • T) x (Y x) (cov.toFun Z x (X x)) =
      g x • (extDerivFun (I := I) (fun b => T b (Y b) (Z b)) x (X x)
        - T x (cov.toFun Y x (X x)) (Z x)
        - T x (Y x) (cov.toFun Z x (X x))) +
      extDerivFun (I := I) g x (X x) • T x (Y x) (Z x)
    set h : M → ℝ := fun b => T b (Y b) (Z b) with hh_def
    have hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x :=
      mdifferentiableAt_tensor02_pairing hT_t hY hZ
    have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g x := hg
    have hpair_eq : (fun b : M => (g • T) b (Y b) (Z b)) = (fun b : M => g b * h b) := by
      funext b
      change (g • T) b (Y b) (Z b) = g b * h b
      have : (g • T) b = g b • T b := rfl
      rw [this, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hpair_eq, extDerivFun_mul_apply hg' hh]
    have h_smul_one : (g • T) x (cov.toFun Y x (X x)) (Z x) =
        g x • T x (cov.toFun Y x (X x)) (Z x) := by
      have : (g • T) x = g x • T x := rfl
      rw [this, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    have h_smul_two : (g • T) x (Y x) (cov.toFun Z x (X x)) =
        g x • T x (Y x) (cov.toFun Z x (X x)) := by
      have : (g • T) x = g x • T x := rfl
      rw [this, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    rw [h_smul_one, h_smul_two]
    have hhx : h x = T x (Y x) (Z x) := rfl
    rw [hhx]
    simp only [smul_eq_mul]
    ring

def tensor02Cov
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    CovariantDerivative I (E →L[ℝ] E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) where
  toFun := tensor02CovFun cov
  isCovariantDerivativeOnUniv := tensor02CovFun_isCovariantDerivativeOn cov

omit [NeZero (Module.finrank ℝ E)] in
lemma tensor02Cov_toFun
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    (tensor02Cov cov).toFun = tensor02CovFun cov := by rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensor02Cov_pairing
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hT : MDiffAtTensor02 T x)
    {Y Z : Π x : M, TangentSpace I x}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x)
    (v : TangentSpace I x) :
    extDerivFun (I := I) (fun b => T b (Y b) (Z b)) x v =
      ((tensor02Cov cov).toFun T x v) (Y x) (Z x)
        + T x (cov.toFun Y x v) (Z x)
        + T x (Y x) (cov.toFun Z x v) := by
  classical
  set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
  have hX : MDiffAt (T% X) x := mdifferentiableAt_extend ..
  have hXx : X x = v := by simp [X]
  rw [show v = X x from hXx.symm]
  rw [tensor02Cov_toFun, tensor02CovFun_apply,
      tensor02CovAt_apply_of_diff_extend cov hT hX hY hZ]
  unfold tensor02Scalar
  ring

variable [SigmaCompactSpace M] [T2Space M]

variable [BoundarylessManifold I M]

def metricTensor02 (g : SmoothRiemannianMetric I M) :
    Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  fun x => g.inner x

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma metricTensor02_apply
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    metricTensor02 g x v w = g.inner x v w := rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma metricTensor02_mdiff
    (g : SmoothRiemannianMetric I M) (x : M) :
    MDiffAtTensor02 (metricTensor02 (I := I) g) x := by
  have hg : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (g.inner b)) := g.contMDiff
  exact (hg x).mdifferentiableAt (by simp)

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem tensor02Cov_metric_zero
    (g : SmoothRiemannianMetric I M) (x : M) (v y z : TangentSpace I x) :
    ((tensor02Cov (LeviCivita (I := I) g)).toFun (metricTensor02 (I := I) g) x v) y z = 0 := by
  classical
  set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
  set Z : Π x : M, TangentSpace I x := FiberBundle.extend E z
  have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
  have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend ..
  have hYx : Y x = y := by simp [Y]
  have hZx : Z x = z := by simp [Z]
  rw [show y = Y x from hYx.symm, show z = Z x from hZx.symm]
  have hT : MDiffAtTensor02 (metricTensor02 (I := I) g) x :=
    metricTensor02_mdiff (I := I) g x
  have hpair :=
    tensor02Cov_pairing (LeviCivita (I := I) g) hT hY hZ v
  have hpair_eq : (fun b : M => (metricTensor02 (I := I) g) b (Y b) (Z b)) =
      (fun b : M => g.inner b (Y b) (Z b)) := by
    funext b; rfl
  rw [hpair_eq] at hpair
  have hMC :=
    (LeviCivita_isMetricCompatible (I := I) g) hY hZ (Set.mem_univ x) v
  have hext_eq : extDerivFun (I := I) (fun b => g.inner b (Y b) (Z b)) x v =
      (mfderiv I 𝓘(ℝ) (fun b : M => g.inner b (Y b) (Z b)) x) v := rfl
  rw [hext_eq] at hpair
  have h_match_one : (metricTensor02 (I := I) g) x ((LeviCivita (I := I) g).toFun Y x v) (Z x) =
      g.inner x ((LeviCivita (I := I) g).toFun Y x v) (Z x) := rfl
  have h_match_two : (metricTensor02 (I := I) g) x (Y x) ((LeviCivita (I := I) g).toFun Z x v) =
      g.inner x (Y x) ((LeviCivita (I := I) g).toFun Z x v) := rfl
  rw [h_match_one, h_match_two] at hpair
  have heq := hpair.symm.trans hMC
  linear_combination heq

def abstractHessian
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) :
    Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  fun x => (cotangentCov (LeviCivita (I := I) g)).toFun (extDerivFun (I := I) f) x

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma abstractHessian_apply
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) (v w : TangentSpace I x) :
    abstractHessian (I := I) g f x v w =
      ((cotangentCov (LeviCivita (I := I) g)).toFun
        (extDerivFun (I := I) f) x v) w := rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem tensor02Cov_apply_one_contMDiff
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (T b)))
    {Y : Π x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Y b))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (T b (Y b))) :=
  ContMDiff.clm_bundle_apply
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (b := fun b : M => b)
    (ϕ := fun b => T b) (v := fun b => Y b) hT hY

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem tensor02Cov_pairing_contMDiff
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (T b)))
    {Y Z : Π x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Y b)))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b (Z b))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => T b (Y b) (Z b)) :=
  cotangentCov_pairing_contMDiff (tensor02Cov_apply_one_contMDiff hT hY) hZ

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private theorem tensor02Cov_triple_apply_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {T : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}
    (hT : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b (T b)))
    (Y Z W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => (((tensor02Cov cov).toFun T x (Y x)) (Z x)) (W x)) := by
  have h_eq : ∀ x : M,
      (((tensor02Cov cov).toFun T x (Y x)) (Z x)) (W x) =
        extDerivFun (I := I) (fun b => T b (Z b) (W b)) x (Y x)
          - T x (cov.toFun Z x (Y x)) (W x)
          - T x (Z x) (cov.toFun W x (Y x)) := by
    intro x
    have hTx : MDiffAtTensor02 T x := (hT x).mdifferentiableAt (by simp)
    have hYx : MDiffAt (T% (fun y : M => Y y)) x :=
      (Y.contMDiff x).mdifferentiableAt (by simp)
    have hZx : MDiffAt (T% (fun y : M => Z y)) x :=
      (Z.contMDiff x).mdifferentiableAt (by simp)
    have hWx : MDiffAt (T% (fun y : M => W y)) x :=
      (W.contMDiff x).mdifferentiableAt (by simp)
    have h := tensor02CovAt_apply_of_diff_extend cov hTx hYx hZx hWx
    rw [tensor02Cov_toFun, tensor02CovFun_apply]
    rw [h]
    rfl
  have h_pair_TZW : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => T b (Z b) (W b)) :=
    tensor02Cov_pairing_contMDiff hT Z.contMDiff W.contMDiff
  have h_extDeriv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x)
        x (extDerivFun (I := I) (fun b => T b (Z b) (W b)) x)) :=
    cotangentCov_extDerivFun_smooth h_pair_TZW
  have h_extDeriv_Y : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => extDerivFun (I := I) (fun b => T b (Z b) (W b)) x (Y x)) := by
    have hap : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun x => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) x
          (extDerivFun (I := I) (fun b => T b (Z b) (W b)) x (Y x))) :=
      ContMDiff.clm_bundle_apply
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => (Bundle.Trivial M ℝ) x)
        (b := fun x : M => x)
        (ϕ := fun x => extDerivFun (I := I) (fun b => T b (Z b) (W b)) x)
        (v := fun x => Y x) h_extDeriv Y.contMDiff
    intro x
    exact (contMDiffAt_section (F := ℝ) (E := Bundle.Trivial M ℝ) x).mp (hap x)
  have h_covZ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) x
        (cov.toFun Z x)) :=
    cotangentCov_covApply_smooth cov Z.contMDiff
  have h_covZY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E (E := TangentSpace I) x (cov.toFun Z x (Y x))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x)
      (b := fun x : M => x)
      (ϕ := fun x => cov.toFun Z x) (v := fun x => Y x) h_covZ Y.contMDiff
  have h_T_covZY_W : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => T x (cov.toFun Z x (Y x)) (W x)) :=
    tensor02Cov_pairing_contMDiff hT h_covZY W.contMDiff
  have h_covW : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) x
        (cov.toFun W x)) :=
    cotangentCov_covApply_smooth cov W.contMDiff
  have h_covWY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E (E := TangentSpace I) x (cov.toFun W x (Y x))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun x : M => TangentSpace I x)
      (b := fun x : M => x)
      (ϕ := fun x => cov.toFun W x) (v := fun x => Y x) h_covW Y.contMDiff
  have h_T_Z_covWY : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => T x (Z x) (cov.toFun W x (Y x))) :=
    tensor02Cov_pairing_contMDiff hT Z.contMDiff h_covWY
  have h_combined : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => extDerivFun (I := I) (fun b => T b (Z b) (W b)) x (Y x)
        - T x (cov.toFun Z x (Y x)) (W x)
        - T x (Z x) (cov.toFun W x (Y x))) :=
    (h_extDeriv_Y.sub h_T_covZY_W).sub h_T_Z_covWY
  refine h_combined.congr ?_
  intro x
  exact h_eq x

set_option maxHeartbeats 800000 in

instance tensor02Cov_isContMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative.ContMDiffCovariantDerivative (tensor02Cov cov) ∞ where
  contMDiff :=
    { contMDiff := by
        intro T hT
        have hT_inf : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
            (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
              (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
              (T x)) := by
          have h_le : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) + 1 := by
            rw [ENat.coe_top_add_one]
          exact contMDiffOn_univ.mp (hT.of_le h_le)
        have hglobal : ContMDiff I
            (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))) ∞
            (fun x : M => TotalSpace.mk'
              (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ)))
              (E := fun x : M => TangentSpace I x →L[ℝ]
                (TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ))) x
              ((tensor02Cov cov).toFun T x)) := by
          apply cotangentCov_clmSection_smooth_aux
            (V₂ := fun x : M => TangentSpace I x →L[ℝ]
              (TangentSpace I x →L[ℝ] ℝ))
            (φ := fun x => (tensor02Cov cov).toFun T x)
          intro Y
          apply cotangentCov_clmSection_smooth_aux
            (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
            (φ := fun x => (tensor02Cov cov).toFun T x (Y x))
          intro Z
          apply cotangentCov_clmSection_smooth_aux
            (V₂ := fun _ : M => ℝ)
            (φ := fun x => ((tensor02Cov cov).toFun T x (Y x)) (Z x))
          intro W
          have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
              (fun x => (((tensor02Cov cov).toFun T x (Y x)) (Z x)) (W x)) :=
            tensor02Cov_triple_apply_smooth cov hT_inf Y Z W
          intro x
          rw [contMDiffAt_section]
          refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
          filter_upwards with y
          change (((tensor02Cov cov).toFun T y (Y y)) (Z y)) (W y) =
            (trivializationAt ℝ (Bundle.Trivial M ℝ) x
              ⟨y, (((tensor02Cov cov).toFun T y (Y y)) (Z y)) (W y)⟩).2
          rfl
        exact hglobal.contMDiffOn }

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem abstractHessian_symm
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (v w : TangentSpace I x) :
    abstractHessian (I := I) g f x v w = abstractHessian (I := I) g f x w v := by
  classical
  set V : Π x : M, TangentSpace I x := FiberBundle.extend E v with hV_def
  set W : Π x : M, TangentSpace I x := FiberBundle.extend E w with hW_def
  have hV : MDiffAt (T% V) x := mdifferentiableAt_extend ..
  have hW : MDiffAt (T% W) x := mdifferentiableAt_extend ..
  have hVx : V x = v := by simp [V]
  have hWx : W x = w := by simp [W]
  have hf_cmd1 : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) 1
      (inTangentCoordinates I 𝓘(ℝ, ℝ) id f (mfderiv I 𝓘(ℝ, ℝ) f) x) x := by
    have := hf.mfderiv_const (m := 1) (le_refl _)
    simpa using this
  have hθ : MDiffAtCotangent (extDerivFun (I := I) f) x := by
    change MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b
        (extDerivFun (I := I) f b)) x
    rw [mdifferentiableAt_hom_bundle]
    refine ⟨mdifferentiableAt_id, ?_⟩
    have hcoord_mdiff : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] ℝ)
        (inTangentCoordinates I 𝓘(ℝ, ℝ) id f (mfderiv I 𝓘(ℝ, ℝ) f) x) x :=
      hf_cmd1.mdifferentiableAt (by norm_num)
    refine hcoord_mdiff.congr_of_eventuallyEq ?_
    filter_upwards with y
    simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
      Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.continuousLinearMapAt_trivialization,
      TangentBundle.continuousLinearMapAt_model_space,
      extDerivFun, id_eq]
    rfl
  have hpair_v :=
    cotangentCov_dualPairing (LeviCivita (I := I) g) hθ hW v
  have hpair_w :=
    cotangentCov_dualPairing (LeviCivita (I := I) g) hθ hV w
  have hH_v : abstractHessian (I := I) g f x v w =
      extDerivFun (I := I) (fun b => extDerivFun (I := I) f b (W b)) x v -
        extDerivFun (I := I) f x ((LeviCivita (I := I) g).toFun W x v) := by
    change ((cotangentCov (LeviCivita (I := I) g)).toFun
      (extDerivFun (I := I) f) x v) w = _
    rw [show w = W x from hWx.symm]
    have := hpair_v
    linarith [this]
  have hH_w : abstractHessian (I := I) g f x w v =
      extDerivFun (I := I) (fun b => extDerivFun (I := I) f b (V b)) x w -
        extDerivFun (I := I) f x ((LeviCivita (I := I) g).toFun V x w) := by
    change ((cotangentCov (LeviCivita (I := I) g)).toFun
      (extDerivFun (I := I) f) x w) v = _
    rw [show v = V x from hVx.symm]
    have := hpair_w
    linarith [this]
  rw [hH_v, hH_w]
  have hx_int : extChartAt I x x ∈ interior ((extChartAt I x).target : Set E) :=
    (I.isInteriorPoint_iff (x := x)).mp BoundarylessManifold.isInteriorPoint
  have hfound :
      extDerivFun (I := I) f x (VectorField.mlieBracket I V W x) =
        extDerivFun (I := I) (fun b => extDerivFun (I := I) f b (W b)) x (V x) -
          extDerivFun (I := I) (fun b => extDerivFun (I := I) f b (V b)) x (W x) :=
    extDerivFun_apply_mlieBracket hV hW hf hx_int
  have htor : (LeviCivita (I := I) g).torsion = 0 :=
    LeviCivita_torsion_eq_zero (I := I) g
  have hbr :
      (LeviCivita (I := I) g).toFun W x (V x) -
        (LeviCivita (I := I) g).toFun V x (W x) =
      VectorField.mlieBracket I V W x :=
    (CovariantDerivative.torsion_eq_zero_iff
      (cov := LeviCivita (I := I) g)).mp htor hV hW
  rw [hVx, hWx] at hfound
  rw [hVx, hWx] at hbr
  have hcov_diff :
      extDerivFun (I := I) f x ((LeviCivita (I := I) g).toFun W x v) -
        extDerivFun (I := I) f x ((LeviCivita (I := I) g).toFun V x w) =
      extDerivFun (I := I) f x (VectorField.mlieBracket I V W x) := by
    rw [← map_sub]
    rw [hbr]
  linarith [hfound, hcov_diff]

end Connection
end Integral
end DifferentialGeometry
