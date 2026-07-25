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

local instance cotangentFiberBundle :
    FiberBundle (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  inferInstance

local instance cotangentVectorBundle :
    VectorBundle ℝ (E →L[ℝ] ℝ) (fun x : M => TangentSpace I x →L[ℝ] ℝ) :=
  inferInstance

def MDiffAtCotangent
    (θ : Π x : M, TangentSpace I x →L[ℝ] ℝ) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
    (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
      (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (θ b)) x

def cotangentScalar
    (cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    (θ : Π x : M, TangentSpace I x →L[ℝ] ℝ) (x : M)
    (X Y : Π x : M, TangentSpace I x) : ℝ :=
  extDerivFun (I := I) (fun b => θ b (Y b)) x (X x) - θ x (cov Y x (X x))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
lemma cotangentScalar_def
    (cov : (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    (θ : Π x : M, TangentSpace I x →L[ℝ] ℝ) (x : M)
    (X Y : Π x : M, TangentSpace I x) :
    cotangentScalar cov θ x X Y =
      extDerivFun (I := I) (fun b => θ b (Y b)) x (X x) - θ x (cov Y x (X x)) := rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] in
lemma extDerivFun_mul_apply
    {p q : M → ℝ} {x : M}
    (hp : MDifferentiableAt I 𝓘(ℝ, ℝ) p x) (hq : MDifferentiableAt I 𝓘(ℝ, ℝ) q x)
    (v : TangentSpace I x) :
    extDerivFun (I := I) (fun b => p b * q b) x v =
      p x * extDerivFun (I := I) q x v + q x * extDerivFun (I := I) p x v := by
  let mp : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) p x
  let mq : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) q x
  let mpq : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) (fun b : M => p b * q b) x
  have hLeib : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun b : M => p b * q b) x
      (p x • mq + q x • mp) := hp.hasMFDerivAt.mul hq.hasMFDerivAt
  have hmf : mpq = p x • mq + q x • mp := hLeib.mfderiv
  have hmf_v : mpq v = p x • mq v + q x • mp v := by
    have := congrArg (fun (L : TangentSpace I x →L[ℝ] ℝ) => L v) hmf
    simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply] using this
  change mpq v = p x * mq v + q x * mp v
  rw [hmf_v]
  rw [smul_eq_mul, smul_eq_mul]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma mdifferentiableAt_pairing
    {θ : Π x : M, TangentSpace I x →L[ℝ] ℝ}
    {Y : Π x : M, TangentSpace I x} {x : M}
    (hθ : MDiffAtCotangent θ x) (hY : MDiffAt (T% Y) x) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => θ b (Y b)) x := by
  have h : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun m => TotalSpace.mk' ℝ (E := fun _ : M => ℝ) m (θ m (Y m))) x :=
    MDifferentiableAt.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun _ : M => ℝ)
      (b := fun b : M => b)
      (ϕ := fun b => θ b) (v := fun b => Y b) hθ hY
  rw [mdifferentiableAt_totalSpace] at h
  exact h.2

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma cotangentScalar_tensorialAt_X
    (_covOn : IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (cov : (Π x : M, TangentSpace I x) →
        (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
      Set.univ)
    (θ : Π x : M, TangentSpace I x →L[ℝ] ℝ)
    (x : M) (Y : Π x : M, TangentSpace I x)
    (_hY : MDiffAt (T% Y) x) :
    TensorialAt I E (cotangentScalar cov θ x · Y) x where
  smul {f X} _hf _hX := by
    classical
    unfold cotangentScalar
    have hfX : (f • X) x = f x • X x := rfl
    rw [hfX]
    rw [(extDerivFun (I := I) (fun b => θ b (Y b)) x).map_smul,
        ContinuousLinearMap.map_smul, map_smul]
    rw [smul_sub]
  add {X X'} _hX _hX' := by
    classical
    unfold cotangentScalar
    have hXX' : (X + X') x = X x + X' x := rfl
    rw [hXX', map_add, ContinuousLinearMap.map_add, map_add]
    abel

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma cotangentScalar_tensorialAt_Y
    (covOn : IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (cov : (Π x : M, TangentSpace I x) →
        (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
      Set.univ)
    {θ : Π x : M, TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hθ : MDiffAtCotangent θ x)
    (X : Π x : M, TangentSpace I x)
    (_hX : MDiffAt (T% X) x) :
    TensorialAt I E (cotangentScalar cov θ x X ·) x where
  smul {g Y} hg hY := by
    classical
    set h : M → ℝ := fun b => θ b (Y b) with hh_def
    have hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x := mdifferentiableAt_pairing hθ hY
    have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g x := hg
    have hfun : (fun b : M => θ b ((g • Y) b)) = (fun b : M => g b * h b) := by
      funext b
      change θ b ((g • Y) b) = g b * h b
      have : (g • Y) b = g b • Y b := rfl
      rw [this, ContinuousLinearMap.map_smul, smul_eq_mul]
    change extDerivFun (I := I) (fun b => θ b ((g • Y) b)) x (X x) -
        θ x (cov (g • Y) x (X x)) =
      g x • (extDerivFun (I := I) h x (X x) - θ x (cov Y x (X x)))
    rw [hfun, extDerivFun_mul_apply hg' hh, covOn.leibniz hY hg (Set.mem_univ x)]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
    have hhx : h x = θ x (Y x) := rfl
    rw [hhx]
    change g x * extDerivFun (I := I) h x (X x) +
        θ x (Y x) * extDerivFun (I := I) g x (X x) -
        (g x • θ x (cov Y x (X x)) + θ x (extDerivFun (I := I) g x (X x) • Y x)) =
      g x • (extDerivFun (I := I) h x (X x) - θ x (cov Y x (X x)))
    rw [θ x |>.map_smul]
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  add {Y Y'} hY hY' := by
    classical
    change extDerivFun (I := I) (fun b => θ b ((Y + Y') b)) x (X x) -
        θ x (cov (Y + Y') x (X x)) =
      (extDerivFun (I := I) (fun b => θ b (Y b)) x (X x) - θ x (cov Y x (X x))) +
      (extDerivFun (I := I) (fun b => θ b (Y' b)) x (X x) - θ x (cov Y' x (X x)))
    have hadd_fun : (fun b : M => θ b ((Y + Y') b)) =
        (fun b : M => θ b (Y b)) + (fun b : M => θ b (Y' b)) := by
      funext b
      change θ b ((Y + Y') b) = θ b (Y b) + θ b (Y' b)
      have : (Y + Y') b = Y b + Y' b := rfl
      rw [this, ContinuousLinearMap.map_add]
    have h1 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => θ b (Y b)) x :=
      mdifferentiableAt_pairing hθ hY
    have h2 : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => θ b (Y' b)) x :=
      mdifferentiableAt_pairing hθ hY'
    have hext_add : extDerivFun (I := I) (fun b => θ b ((Y + Y') b)) x =
        extDerivFun (I := I) (fun b => θ b (Y b)) x +
        extDerivFun (I := I) (fun b => θ b (Y' b)) x := by
      rw [hadd_fun, extDerivFun_add h1 h2]
    rw [hext_add, ContinuousLinearMap.add_apply,
        covOn.add hY hY' (Set.mem_univ x), ContinuousLinearMap.add_apply,
        ContinuousLinearMap.map_add]
    abel

def cotangentCovAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (θ : Π x : M, TangentSpace I x →L[ℝ] ℝ) (x : M) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) := by
  classical
  by_cases hθ : MDiffAtCotangent θ x
  · exact TensorialAt.mkHom₂
      (Φ := fun X Y => cotangentScalar (cov.toFun) θ x X Y)
      x
      (fun Y hY => cotangentScalar_tensorialAt_X cov.isCovariantDerivativeOnUniv θ x Y hY)
      (fun X hX => cotangentScalar_tensorialAt_Y cov.isCovariantDerivativeOnUniv hθ X hX)
  · exact 0

omit [NeZero (Module.finrank ℝ E)] in
lemma cotangentCovAt_apply_of_diff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {θ : Π x : M, TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hθ : MDiffAtCotangent θ x)
    {X Y : Π x : M, TangentSpace I x}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    cotangentCovAt cov θ x (X x) (Y x) = cotangentScalar (cov.toFun) θ x X Y := by
  classical
  unfold cotangentCovAt
  rw [dif_pos hθ]
  exact TensorialAt.mkHom₂_apply _ _ hX hY

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma cotangentCovAt_of_not_diff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {θ : Π x : M, TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hθ : ¬ MDiffAtCotangent θ x) :
    cotangentCovAt cov θ x = 0 := by
  classical
  unfold cotangentCovAt
  rw [dif_neg hθ]

def cotangentCovFun
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    (Π x : M, TangentSpace I x →L[ℝ] ℝ) →
      (Π x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ)) :=
  fun θ x => cotangentCovAt cov θ x

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma cotangentCovFun_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (θ : Π x : M, TangentSpace I x →L[ℝ] ℝ) (x : M) :
    cotangentCovFun cov θ x = cotangentCovAt cov θ x := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma cotangentCovFun_isCovariantDerivativeOn
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    IsCovariantDerivativeOn (V := (fun x : M => TangentSpace I x →L[ℝ] ℝ))
      (E →L[ℝ] ℝ)
      (cotangentCovFun cov) Set.univ where
  add {θ θ'} {x} hθ hθ' _hx := by
    classical
    have hθ_cot : MDiffAtCotangent θ x := hθ
    have hθ'_cot : MDiffAtCotangent θ' x := hθ'
    have hsum_θ : MDiffAtCotangent (θ + θ') x := mdifferentiableAt_add_section hθ hθ'
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro y
    set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    have hX : MDiffAt (T% X) x := mdifferentiableAt_extend ..
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
    have hXx : X x = v := by simp [X]
    have hYx : Y x = y := by simp [Y]
    change (cotangentCovFun cov (θ + θ') x) v y =
      ((cotangentCovFun cov θ x) + (cotangentCovFun cov θ' x)) v y
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
    change cotangentCovFun cov (θ + θ') x v y =
      cotangentCovFun cov θ x v y + cotangentCovFun cov θ' x v y
    rw [show v = X x from hXx.symm, show y = Y x from hYx.symm]
    rw [cotangentCovFun_apply, cotangentCovFun_apply, cotangentCovFun_apply]
    rw [cotangentCovAt_apply_of_diff cov hsum_θ hX hY,
        cotangentCovAt_apply_of_diff cov hθ_cot hX hY,
        cotangentCovAt_apply_of_diff cov hθ'_cot hX hY]
    change extDerivFun (I := I) (fun b => (θ + θ') b (Y b)) x (X x) -
        (θ + θ') x (cov.toFun Y x (X x)) =
      (extDerivFun (I := I) (fun b => θ b (Y b)) x (X x) -
        θ x (cov.toFun Y x (X x))) +
      (extDerivFun (I := I) (fun b => θ' b (Y b)) x (X x) -
        θ' x (cov.toFun Y x (X x)))
    have hpair_θ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => θ b (Y b)) x :=
      mdifferentiableAt_pairing hθ_cot hY
    have hpair_θ' : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun b : M => θ' b (Y b)) x :=
      mdifferentiableAt_pairing hθ'_cot hY
    have hpair_eq : (fun b : M => (θ + θ') b (Y b)) =
        (fun b : M => θ b (Y b)) + (fun b : M => θ' b (Y b)) := by
      funext b
      change (θ + θ') b (Y b) = θ b (Y b) + θ' b (Y b)
      have : (θ + θ') b = θ b + θ' b := rfl
      rw [this, ContinuousLinearMap.add_apply]
    have hext_add : extDerivFun (I := I) (fun b => (θ + θ') b (Y b)) x =
        extDerivFun (I := I) (fun b => θ b (Y b)) x +
        extDerivFun (I := I) (fun b => θ' b (Y b)) x := by
      rw [hpair_eq, extDerivFun_add hpair_θ hpair_θ']
    rw [hext_add, ContinuousLinearMap.add_apply]
    have h_omega_add : (θ + θ') x (cov.toFun Y x (X x)) =
        θ x (cov.toFun Y x (X x)) + θ' x (cov.toFun Y x (X x)) := by
      have : (θ + θ') x = θ x + θ' x := rfl
      rw [this, ContinuousLinearMap.add_apply]
    rw [h_omega_add]
    ring
  leibniz {θ g x} hθ hg _hx := by
    classical
    have hθ' : MDiffAtCotangent θ x := hθ
    have hsum_θ : MDiffAtCotangent (g • θ) x := hg.smul_section hθ
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro y
    set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
    set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
    have hX : MDiffAt (T% X) x := mdifferentiableAt_extend ..
    have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
    have hXx : X x = v := by simp [X]
    have hYx : Y x = y := by simp [Y]
    rw [show v = X x from hXx.symm, show y = Y x from hYx.symm]
    rw [cotangentCovFun_apply, cotangentCovFun_apply]
    rw [cotangentCovAt_apply_of_diff cov hsum_θ hX hY]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smul_apply]
    rw [cotangentCovAt_apply_of_diff cov hθ' hX hY]
    change extDerivFun (I := I) (fun b => (g • θ) b (Y b)) x (X x) -
        (g • θ) x (cov.toFun Y x (X x)) =
      g x • (extDerivFun (I := I) (fun b => θ b (Y b)) x (X x) -
        θ x (cov.toFun Y x (X x))) +
      extDerivFun g x (X x) • θ x (Y x)
    set h : M → ℝ := fun b => θ b (Y b) with hh_def
    have hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x := mdifferentiableAt_pairing hθ' hY
    have hg' : MDifferentiableAt I 𝓘(ℝ, ℝ) g x := hg
    have hpair_eq : (fun b : M => (g • θ) b (Y b)) = (fun b : M => g b * h b) := by
      funext b
      change (g • θ) b (Y b) = g b * h b
      have : (g • θ) b = g b • θ b := rfl
      rw [this, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hpair_eq, extDerivFun_mul_apply hg' hh]
    have h_g_omega_apply : (g • θ) x (cov.toFun Y x (X x)) =
        g x • θ x (cov.toFun Y x (X x)) := by
      have : (g • θ) x = g x • θ x := rfl
      rw [this, ContinuousLinearMap.smul_apply]
    rw [h_g_omega_apply]
    have hhx : h x = θ x (Y x) := rfl
    rw [hhx]
    simp only [smul_eq_mul]
    ring

def cotangentCov
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    CovariantDerivative I (E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] ℝ) where
  toFun := cotangentCovFun cov
  isCovariantDerivativeOnUniv := cotangentCovFun_isCovariantDerivativeOn cov

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma cotangentCov_toFun
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    (cotangentCov cov).toFun = cotangentCovFun cov := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem cotangentCov_dualPairing
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {θ : Π x : M, TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hθ : MDiffAtCotangent θ x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x)
    (v : TangentSpace I x) :
    extDerivFun (I := I) (fun b => θ b (Y b)) x v =
      ((cotangentCov cov).toFun θ x v) (Y x) + θ x (cov.toFun Y x v) := by
  classical
  set X : Π x : M, TangentSpace I x := FiberBundle.extend E v
  have hX : MDiffAt (T% X) x := mdifferentiableAt_extend ..
  have hXx : X x = v := by simp [X]
  rw [show v = X x from hXx.symm]
  rw [cotangentCov_toFun, cotangentCovFun_apply,
      cotangentCovAt_apply_of_diff cov hθ hX hY]
  change extDerivFun (I := I) (fun b => θ b (Y b)) x (X x) =
      cotangentScalar (cov.toFun) θ x X Y + θ x (cov.toFun Y x (X x))
  unfold cotangentScalar
  ring

variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

def metricFlat (g : SmoothRiemannianMetric I M) (X : Π x : M, TangentSpace I x) :
    Π x : M, TangentSpace I x →L[ℝ] ℝ :=
  fun b => g.inner b (X b)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
@[simp] lemma metricFlat_apply
    (g : SmoothRiemannianMetric I M) (X : Π x : M, TangentSpace I x)
    (b : M) (Y : TangentSpace I b) :
    metricFlat g X b Y = g.inner b (X b) Y := rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma metricFlat_mdiff_total
    (g : SmoothRiemannianMetric I M) {X : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) b (metricFlat g X b)) x := by
  have hg : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) b
        (g.inner b)) x := by
    have := g.contMDiff
    exact (this.contMDiffAt).mdifferentiableAt (by norm_num)
  exact MDifferentiableAt.clm_bundle_apply
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (b := fun b : M => b)
    (ϕ := fun b => g.inner b) (v := fun b => X b) hg hX

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma metricFlat_mdiff
    (g : SmoothRiemannianMetric I M) {X : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) :
    MDiffAtCotangent (metricFlat g X) x :=
  metricFlat_mdiff_total g hX

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem cotangentCov_metricDuality
    (g : SmoothRiemannianMetric I M)
    {X : Π x : M, TangentSpace I x} {x : M} (hX : MDiffAt (T% X) x)
    (v y : TangentSpace I x) :
    ((cotangentCov (LeviCivita (I := I) g)).toFun (metricFlat g X) x v) y =
      g.inner x ((LeviCivita (I := I) g).toFun X x v) y := by
  classical
  set Y : Π x : M, TangentSpace I x := FiberBundle.extend E y
  have hY : MDiffAt (T% Y) x := mdifferentiableAt_extend ..
  have hYx : Y x = y := by simp [Y]
  have hflat : MDiffAtCotangent (metricFlat g X) x := metricFlat_mdiff g hX
  have hpair :=
    cotangentCov_dualPairing (LeviCivita (I := I) g) hflat hY v
  have hpair_eq : (fun b : M => (metricFlat g X) b (Y b)) =
      (fun b : M => g.inner b (X b) (Y b)) := by
    funext b; rfl
  rw [hpair_eq] at hpair
  have hMC :=
    (LeviCivita_isMetricCompatible (I := I) g) hX hY (Set.mem_univ x) v
  have heq := hpair.symm.trans hMC
  have h_flat_apply : (metricFlat g X) x ((LeviCivita (I := I) g).toFun Y x v) =
      g.inner x (X x) ((LeviCivita (I := I) g).toFun Y x v) := rfl
  rw [h_flat_apply] at heq
  rw [hYx] at heq
  exact add_right_cancel heq

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem cotangentCov_clmSection_smooth_aux
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
    [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, TopologicalSpace (V₂ x)]
    [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
    [ContMDiffVectorBundle ∞ F₂ V₂ I]
    [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
    [SigmaCompactSpace M] [T2Space M]
    (φ : ∀ x : M, TangentSpace I x →L[ℝ] V₂ x)
    (h : ∀ (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ContMDiff I (I.prod 𝓘(ℝ, F₂)) ∞
        (fun x => TotalSpace.mk' F₂ (E := V₂) x (φ x (Y x)))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F₂)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] F₂)
        (E := fun x : M => TangentSpace I x →L[ℝ] V₂ x) x (φ x)) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_pointwise (IB := I) (X := M)
  intro v
  let e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀
  let e₂ := trivializationAt F₂ V₂ x₀
  let b := Module.finBasis ℝ E
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have he₂ : x₀ ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ V₂ x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hφY : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, F₂)) ∞
      (fun x => TotalSpace.mk' F₂ (E := V₂) x (φ x (Y i x))) := fun i => h (Y i)
  have hφY_fiber : ∀ i, ContMDiffAt I 𝓘(ℝ, F₂) ∞
      (fun x => (e₂ ⟨x, φ x (Y i x)⟩).2) x₀ := fun i => by
    have hi := (contMDiffAt_section (F := F₂) (E := V₂) x₀).mp ((hφY i) x₀)
    simpa [e₂, trivializationAt] using hi
  have hsum : ContMDiffAt I 𝓘(ℝ, F₂) ∞
      (fun x => ∑ i, b.repr v i • (e₂ ⟨x, φ x (Y i x)⟩).2) x₀ := by
    apply ContMDiffAt.sum
    intro i _
    exact (contMDiffAt_const (c := (b.repr v i : ℝ))).smul (hφY_fiber i)
  refine hsum.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet :=
    e₁.open_baseSet.mem_nhds he₁
  have h_base₂ : ∀ᶠ x in 𝓝 x₀, x ∈ e₂.baseSet :=
    e₂.open_baseSet.mem_nhds he₂
  filter_upwards [h_base₁, h_base₂, hY] with x hx₁ hx₂ hYx
  have hv_decomp : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  have h_inCoord :
      (ContinuousLinearMap.inCoordinates E (TangentSpace I) F₂ V₂ x₀ x x₀ x (φ x)) v =
      e₂.continuousLinearMapAt ℝ x ((φ x) (e₁.symmL ℝ x v)) := rfl
  rw [h_inCoord]
  have h₁ : e₁.symmL ℝ x v = ∑ i, (b.repr v) i • e₁.symmL ℝ x (b i) := by
    conv_lhs => rw [hv_decomp]
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  have h₂ : (φ x) (∑ i, (b.repr v) i • e₁.symmL ℝ x (b i)) =
      ∑ i, (b.repr v) i • (φ x) (e₁.symmL ℝ x (b i)) := by
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  have h₃ : e₂.continuousLinearMapAt ℝ x
        (∑ i, (b.repr v) i • (φ x) (e₁.symmL ℝ x (b i))) =
      ∑ i, (b.repr v) i • e₂.continuousLinearMapAt ℝ x ((φ x) (e₁.symmL ℝ x (b i))) := by
    rw [map_sum]; congr 1; ext i; rw [map_smul]
  rw [h₁, h₂, h₃]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  have h_lf : e₁.symmL ℝ x (b i) = (Y i) x := by
    rw [hYx i]
    rw [Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  rw [h_lf]
  change (Trivialization.continuousLinearMapAt ℝ e₂ x) ((φ x) ((Y i) x)) = _
  rw [show ⇑(e₂.continuousLinearMapAt ℝ x) = ⇑(e₂.linearMapAt ℝ x) from rfl,
    e₂.coe_linearMapAt_of_mem hx₂]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem cotangentCov_extDerivFun_smooth
    {h : M → ℝ} (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => (TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x))
        x (extDerivFun h x)) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_pointwise (IB := I) (X := M)
  intro v
  have hmfderiv : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) ∞
      (inTangentCoordinates I 𝓘(ℝ, ℝ) id h (mfderiv I 𝓘(ℝ, ℝ) h) x₀) x₀ :=
    hh.contMDiffAt.mfderiv_const (le_refl _)
  have hmfderiv_v : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x => inTangentCoordinates I 𝓘(ℝ, ℝ) id h (mfderiv I 𝓘(ℝ, ℝ) h) x₀ x v) x₀ :=
    ((ContinuousLinearMap.apply ℝ ℝ v).contMDiff.contMDiffAt).comp x₀ hmfderiv
  convert hmfderiv_v using 1
  ext x
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    TangentBundle.continuousLinearMapAt_model_space,
    extDerivFun, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_id', id_eq]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem cotangentCov_pairing_contMDiff
    {θ : Π x : M, TangentSpace I x →L[ℝ] ℝ}
    (hθ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) x (θ x)))
    {Y : Π x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x))) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => θ x (Y x)) := by
  have hap : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun x => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) x (θ x (Y x))) :=
    ContMDiff.clm_bundle_apply
      (E₁ := fun x : M => TangentSpace I x)
      (E₂ := fun _ : M => ℝ)
      (b := fun x : M => x)
      (ϕ := fun x => θ x) (v := fun x => Y x) hθ hY
  intro x
  exact (contMDiffAt_section (F := ℝ) (E := Bundle.Trivial M ℝ) x).mp (hap x)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem cotangentCov_covApply_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {Y : Π x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) x (cov.toFun Y x)) := by
  have hY' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1)
      (fun x : M => TotalSpace.mk' E (E := TangentSpace I) x (Y x)) Set.univ := by
    have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact (hY.of_le h_le).contMDiffOn
  have hres := hcov.contMDiff.contMDiff (σ := Y) hY'
  intro x
  exact (hres x (Set.mem_univ x)).contMDiffAt Filter.univ_mem

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem cotangentCov_double_apply_smooth
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    {θ : Π x : M, TangentSpace I x →L[ℝ] ℝ}
    (hθ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) x (θ x)))
    (Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => ((cotangentCov cov).toFun θ x (Y x)) (Z x)) := by
  have h_eq : ∀ x : M,
      ((cotangentCov cov).toFun θ x (Y x)) (Z x) =
        extDerivFun (I := I) (fun b => θ b (Z b)) x (Y x) -
          θ x (cov.toFun Z x (Y x)) := by
    intro x
    have hθx : MDiffAtCotangent θ x := (hθ x).mdifferentiableAt (by simp)
    have hYx : MDiffAt (T% (fun y : M => Y y)) x :=
      (Y.contMDiff x).mdifferentiableAt (by simp)
    have hZx : MDiffAt (T% (fun y : M => Z y)) x :=
      (Z.contMDiff x).mdifferentiableAt (by simp)
    have := cotangentCovAt_apply_of_diff cov hθx hYx hZx
    rw [cotangentCov_toFun, cotangentCovFun_apply]
    rw [this]
    rfl
  have h_pair_θZ : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun b : M => θ b (Z b)) :=
    cotangentCov_pairing_contMDiff hθ Z.contMDiff
  have h_extDeriv : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] (Bundle.Trivial M ℝ) x)
        x (extDerivFun (I := I) (fun b => θ b (Z b)) x)) :=
    cotangentCov_extDerivFun_smooth h_pair_θZ
  have h_extDeriv_Y : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => extDerivFun (I := I) (fun b => θ b (Z b)) x (Y x)) := by
    have hap : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun x => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) x
          (extDerivFun (I := I) (fun b => θ b (Z b)) x (Y x))) :=
      ContMDiff.clm_bundle_apply
        (E₁ := fun x : M => TangentSpace I x)
        (E₂ := fun x : M => (Bundle.Trivial M ℝ) x)
        (b := fun x : M => x)
        (ϕ := fun x => extDerivFun (I := I) (fun b => θ b (Z b)) x)
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
  have h_θ_covZY : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => θ x (cov.toFun Z x (Y x))) :=
    cotangentCov_pairing_contMDiff hθ h_covZY
  have h_combined : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => extDerivFun (I := I) (fun b => θ b (Z b)) x (Y x) -
        θ x (cov.toFun Z x (Y x))) :=
    h_extDeriv_Y.sub h_θ_covZY
  refine h_combined.congr ?_
  intro x
  exact h_eq x

instance cotangentCov_isContMDiff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [hcov : CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative.ContMDiffCovariantDerivative (cotangentCov cov) ∞ where
  contMDiff :=
    { contMDiff := by
        intro θ hθ
        have hθ_inf : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
            (fun x : M => TotalSpace.mk' (E →L[ℝ] ℝ)
              (E := fun x : M => TangentSpace I x →L[ℝ] ℝ) x (θ x)) := by
          have h_le : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) + 1 := by
            rw [ENat.coe_top_add_one]
          exact contMDiffOn_univ.mp (hθ.of_le h_le)
        have hglobal : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] ℝ))) ∞
            (fun x : M => TotalSpace.mk'
              (E →L[ℝ] (E →L[ℝ] ℝ))
              (E := fun x : M => TangentSpace I x →L[ℝ]
                (TangentSpace I x →L[ℝ] ℝ)) x
              ((cotangentCov cov).toFun θ x)) := by
          apply cotangentCov_clmSection_smooth_aux
            (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
            (φ := fun x => (cotangentCov cov).toFun θ x)
          intro Y
          apply cotangentCov_clmSection_smooth_aux
            (V₂ := fun _ : M => ℝ)
            (φ := fun x => (cotangentCov cov).toFun θ x (Y x))
          intro Z
          have h_scalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
              (fun x => ((cotangentCov cov).toFun θ x (Y x)) (Z x)) :=
            cotangentCov_double_apply_smooth cov hθ_inf Y Z
          intro x
          rw [contMDiffAt_section]
          refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
          filter_upwards with y
          change ((cotangentCov cov).toFun θ y (Y y)) (Z y) =
            (trivializationAt ℝ (Bundle.Trivial M ℝ) x
              ⟨y, ((cotangentCov cov).toFun θ y (Y y)) (Z y)⟩).2
          rfl
        exact hglobal.contMDiffOn }

end Connection
end Integral
end DifferentialGeometry
