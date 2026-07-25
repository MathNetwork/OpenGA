import DifferentialGeometry.Tensor.RSTensor.Basis
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Connection.Smooth
import Mathlib.Geometry.Manifold.VectorBundle.Hom

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.flexible false









noncomputable section

namespace DifferentialGeometry

open Bundle
open Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]









omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem covariantDerivative_finset_sum_tangent
    {ι : Type*} (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (t : Finset ι) (σ : ι → (x : M) → TangentSpace I x)
    {x : M} (v : TangentSpace I x)
    (hσ : ∀ i, MDiffAt (T% (σ i)) x) :
    (cov (t.sum σ) x) v = t.sum (fun i => (cov (σ i) x) v) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp [cov.isCovariantDerivativeOnUniv.zero]
  | insert i t hit ih =>
      have hσi : MDiffAt (T% (σ i)) x := hσ i
      have hsum : MDiffAt (T% (t.sum σ)) x := by
        have hsum_raw := MDifferentiableAt.sum_section (s := t) (t := σ) hσ
        simpa using hsum_raw
      calc
        (cov ((insert i t).sum σ) x) v
            = (cov (σ i + t.sum σ) x) v := by
              simp [Finset.sum_insert, hit]
        _ = ((cov (σ i) x + cov (t.sum σ) x) v) := by
              rw [cov.isCovariantDerivativeOnUniv.add hσi hsum]
        _ = (cov (σ i) x) v + (cov (t.sum σ) x) v := by
              simp
        _ = (insert i t).sum (fun j => (cov (σ j) x) v) := by
              rw [ih]
              simp [Finset.sum_insert, hit]

omit [CompleteSpace E] in
theorem covariantDerivative_localFrame_coeff_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x) (i k : ι) :
    e.localFrame_coeff I b k x
        ((cov σ x) (e.localFrame b i x)) =
      extDerivFun (I := I) ((LinearMap.piApply (e.localFrame_coeff I b k)) σ)
        x (e.localFrame b i x) +
        ∑ j : ι,
          e.localFrame_coeff I b j x (σ x) *
            e.localFrame_coeff I b k x
              ((cov (e.localFrame b j) x) (e.localFrame b i x)) := by
  classical
  let frame : ι → (x : M) → TangentSpace I x := fun j => e.localFrame b j
  let coeff : ι → M → Real := fun j y => e.localFrame_coeff I b j y (σ y)
  let term : ι → (x : M) → TangentSpace I x := fun j => coeff j • frame j
  have hframe_diff (j : ι) : MDiffAt (T% (fun y => frame j y)) x := by
    simpa [frame] using
      ((e.isLocalFrameOn_localFrame_baseSet I ∞ b).contMDiffAt
        e.open_baseSet hx j).mdifferentiableAt (by simp)
  have hcoeff_diff (j : ι) :
      MDifferentiableAt I 𝓘(Real, Real) (coeff j) x := by
    simpa [coeff] using
      mdifferentiableAt_localFrame_coeff
        (I := I) (e := e) (b := b) hx hσ j
  have hterm_diff (j : ι) : MDiffAt (T% (fun y => term j y)) x := by
    exact (hcoeff_diff j).smul_section (hframe_diff j)
  have hsum_diff :
      MDiffAt (T% ((Finset.univ : Finset ι).sum term)) x := by
    simpa using
      MDifferentiableAt.sum_section
        (s := (Finset.univ : Finset ι)) (t := term) hterm_diff
  have hσ_ev :
      σ =ᶠ[𝓝 x] fun y : M => ∑ j : ι, term j y := by
    simpa [term, coeff, frame] using
      e.eventually_eq_localFrame_sum_coeff_smul (I := I) b hx (s := σ)
  have hcov_congr :
      cov σ x = cov ((Finset.univ : Finset ι).sum term) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσ hsum_diff
      (by simp) (by simpa using hσ_ev)
  have hcov_sum :
      (cov σ x) (frame i x) =
        ∑ j : ι,
          (extDerivFun (I := I) (coeff j) x (frame i x) • frame j x +
            coeff j x • (cov (frame j) x) (frame i x)) := by
    calc
      (cov σ x) (frame i x)
          = (cov ((Finset.univ : Finset ι).sum term) x) (frame i x) := by
            rw [hcov_congr]
      _ = ∑ j : ι, (cov (term j) x) (frame i x) := by
            rw [covariantDerivative_finset_sum_tangent (I := I) cov
              (Finset.univ : Finset ι) term (frame i x) hterm_diff]
      _ = ∑ j : ι,
          (extDerivFun (I := I) (coeff j) x (frame i x) • frame j x +
            coeff j x • (cov (frame j) x) (frame i x)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            have hleib := congr($(cov.isCovariantDerivativeOnUniv.leibniz
              (σ := frame j) (g := coeff j) (x := x)
              (hframe_diff j) (hcoeff_diff j)) (frame i x))
            simpa [term, coeff, frame, add_comm] using hleib
  have hcoeff_frame (j l : ι) :
      e.localFrame_coeff I b l x (frame j x) = (if j = l then 1 else 0) := by
    rw [e.localFrame_coeff_apply_of_mem_baseSet b hx]
    change ((e.basisAt b hx).repr (e.localFrame b j x)) l = (if j = l then 1 else 0)
    rw [e.localFrame_apply_of_mem_baseSet (b := b) hx]
    rw [(e.basisAt b hx).repr_self]
    simp [Finsupp.single_apply]
  rw [hcov_sum]
  rw [map_sum]
  simp only [map_add]
  rw [Finset.sum_add_distrib]
  have hderiv_sum :
      (∑ j : ι,
          e.localFrame_coeff I b k x
            (extDerivFun (I := I) (coeff j) x (frame i x) • frame j x)) =
        extDerivFun (I := I) (coeff k) x (frame i x) := by
    calc
      (∑ j : ι,
          e.localFrame_coeff I b k x
            (extDerivFun (I := I) (coeff j) x (frame i x) • frame j x))
          = ∑ j : ι,
              extDerivFun (I := I) (coeff j) x (frame i x) *
                e.localFrame_coeff I b k x (frame j x) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              simp
      _ = ∑ j : ι,
            extDerivFun (I := I) (coeff j) x (frame i x) *
              (if j = k then 1 else 0) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hcoeff_frame j k]
      _ = extDerivFun (I := I) (coeff k) x (frame i x) := by
              simp
  have hchristoffel_sum :
      (∑ j : ι,
          e.localFrame_coeff I b k x
            (coeff j x • (cov (frame j) x) (frame i x))) =
        ∑ j : ι,
          coeff j x *
            e.localFrame_coeff I b k x ((cov (frame j) x) (frame i x)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  rw [hderiv_sum, hchristoffel_sum]
  rfl







omit [CompleteSpace E] in
theorem covariantDerivative_localFrame_coeff_eq_along
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) (k : ι) :
    e.localFrame_coeff I b k x ((cov σ x) v) =
      extDerivFun (I := I) ((LinearMap.piApply (e.localFrame_coeff I b k)) σ) x v +
        ∑ j : ι,
          e.localFrame_coeff I b j x (σ x) *
            e.localFrame_coeff I b k x
              ((cov (e.localFrame b j) x) v) := by
  classical
  let f : M → Real := (LinearMap.piApply (e.localFrame_coeff I b k)) σ
  let lhs : TangentSpace I x →ₗ[Real] Real :=
    (e.localFrame_coeff I b k x).comp (cov σ x).toLinearMap
  let rhs : TangentSpace I x →ₗ[Real] Real :=
    (extDerivFun (I := I) f x).toLinearMap +
      ∑ j : ι,
        e.localFrame_coeff I b j x (σ x) •
          ((e.localFrame_coeff I b k x).comp (cov (e.localFrame b j) x).toLinearMap)
  have hlin : lhs = rhs := by
    apply (e.basisAt b hx).ext
    intro i
    have hframe : e.basisAt b hx i = e.localFrame b i x := by
      exact (e.localFrame_apply_of_mem_baseSet (b := b) (i := i) hx).symm
    have hbase :=
      covariantDerivative_localFrame_coeff_eq (I := I) cov e b hx hσ i k
    simpa [lhs, rhs, f, hframe, Finset.sum_apply] using hbase
  have happly := congrArg (fun L : TangentSpace I x →ₗ[Real] Real => L v) hlin
  simpa [lhs, rhs, f, Finset.sum_apply] using happly











noncomputable def homModelCoeff
    {ι : Type*} (b : Module.Basis ι Real E) (i k : ι) :
    (E →L[Real] E) →ₗ[Real] Real where
  toFun A := b.coord k (A (b i))
  map_add' A B := by simp
  map_smul' c A := by simp

noncomputable def localHomCoeff
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E) (i k : ι) (x : M) :
    (TangentSpace I x →L[Real] TangentSpace I x) →ₗ[Real] Real :=
  (homModelCoeff (E := E) b i k).comp
    ((e.continuousLinearMap (RingHom.id Real) e).linearMapAt Real x)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem localHomCoeff_apply
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet)
    (A : TangentSpace I x →L[Real] TangentSpace I x) (i k : ι) :
    localHomCoeff (I := I) e b i k x A =
      e.localFrame_coeff I b k x (A (e.localFrame b i x)) := by
  rw [e.localFrame_apply_of_mem_baseSet (b := b) hx]
  have hbasis :
      e.basisAt b hx =
        (e.isLocalFrameOn_localFrame_baseSet I 1 b).toBasisAt hx := by
    ext j
    simp [IsLocalFrameOn.toBasisAt, Bundle.Trivialization.localFrame,
      Bundle.Trivialization.basisAt, hx]
  have hhom : x ∈ (e.continuousLinearMap (RingHom.id Real) e).baseSet := by
    simp [hx]
  simp only [localHomCoeff, homModelCoeff, LinearMap.coe_comp, Function.comp_apply]
  simp only [Bundle.Trivialization.localFrame_coeff, IsLocalFrameOn.coeff, hx, ↓reduceDIte]
  rw [← hbasis]
  rw [((e.continuousLinearMap (RingHom.id Real) e).coe_linearMapAt_of_mem hhom)]
  change
    b.coord k (((e.continuousLinearMap (RingHom.id Real) e) ⟨x, A⟩).2 (b i)) =
      (e.basisAt b hx).coord k (A ((e.basisAt b hx) i))
  rw [Bundle.Trivialization.continuousLinearMap_apply]
  simp [Bundle.Trivialization.basisAt, Bundle.Trivialization.continuousLinearMapAt_apply,
    e.coe_linearMapAt_of_mem hx]

omit [CompleteSpace E] in
theorem homLocalFrameCoeff_eq_localHomCoeff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet)
    (A : TangentSpace I x →L[Real] TangentSpace I x) (i k : ι) :
    (e.continuousLinearMap (RingHom.id Real) e).localFrame_coeff I
        (continuousLinearMap_homBasis (𝕜 := Real) b b) (k, i) x A =
      localHomCoeff (I := I) e b i k x A := by
  let eHom := e.continuousLinearMap (RingHom.id Real) e
  let bHom := continuousLinearMap_homBasis (𝕜 := Real) b b
  have hhom : x ∈ eHom.baseSet := by
    simp [eHom, hx]
  classical
  let s : (y : M) → TangentSpace I y →L[Real] TangentSpace I y :=
    fun y => if h : x = y then h ▸ A else 0
  have hsx : s x = A := by
    simp [s]
  rw [← hsx]
  rw [eHom.localFrame_coeff_apply_of_mem_baseSet bHom hhom s (k, i)]
  simp only [eHom, bHom, hsx]
  simp [Bundle.Trivialization.basisAt, localHomCoeff, homModelCoeff,
    continuousLinearMap_homBasis_repr]
  rw [((e.continuousLinearMap (RingHom.id Real) e).coe_linearMapAt_of_mem hhom)]

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x) (i k : ι) :
    localHomCoeff (I := I) e b i k x (cov σ x) =
      extDerivFun (I := I) ((LinearMap.piApply (e.localFrame_coeff I b k)) σ)
        x (e.localFrame b i x) +
        ∑ j : ι,
          e.localFrame_coeff I b j x (σ x) *
            e.localFrame_coeff I b k x
              ((cov (e.localFrame b j) x) (e.localFrame b i x)) := by
  rw [localHomCoeff_apply (I := I) e b hx (cov σ x) i k]
  exact covariantDerivative_localFrame_coeff_eq (I := I) cov e b hx hσ i k

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_eventuallyEq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y) (i k : ι) :
    (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) =ᶠ[𝓝 x]
      fun y : M =>
        extDerivFun (I := I) ((LinearMap.piApply (e.localFrame_coeff I b k)) σ)
          y (e.localFrame b i y) +
          ∑ j : ι,
            e.localFrame_coeff I b j y (σ y) *
              e.localFrame_coeff I b k y
                ((cov (e.localFrame b j) y) (e.localFrame b i y)) := by
  filter_upwards [e.open_baseSet.mem_nhds hx, hσ] with y hy hσy
  exact covariantDerivative_localHomCoeff_eq (I := I) cov e b hy hσy i k

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_contMDiffAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (i k : ι)
    (hderiv : ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        extDerivFun (I := I) ((LinearMap.piApply (e.localFrame_coeff I b k)) σ)
          y (e.localFrame b i y)) x)
    (hcoeff : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => e.localFrame_coeff I b j y (σ y)) x)
    (hchristoffel : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrame_coeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x := by
  have hEq :=
    covariantDerivative_localHomCoeff_eventuallyEq (I := I) cov e b hx hσ i k
  have hRhs : ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        extDerivFun (I := I) ((LinearMap.piApply (e.localFrame_coeff I b k)) σ)
          y (e.localFrame b i y) +
          ∑ j : ι,
            e.localFrame_coeff I b j y (σ y) *
              e.localFrame_coeff I b k y
                ((cov (e.localFrame b j) y) (e.localFrame b i y))) x := by
    refine hderiv.add ?_
    exact ContMDiffAt.sum fun j _ => (hcoeff j).mul (hchristoffel j)
  exact hRhs.congr_of_eventuallyEq hEq



omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_contMDiffAt_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (i k : ι)
    (hderiv : ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M =>
        extDerivFun (I := I) ((LinearMap.piApply (e.localFrame_coeff I b k)) σ)
          y (e.localFrame b i y)) x)
    (hcoeff : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M => e.localFrame_coeff I b j y (σ y)) x)
    (hchristoffel : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M =>
        e.localFrame_coeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x := by
  have hEq :=
    covariantDerivative_localHomCoeff_eventuallyEq (I := I) cov e b hx hσ i k
  have hRhs : ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M =>
        extDerivFun (I := I) ((LinearMap.piApply (e.localFrame_coeff I b k)) σ)
          y (e.localFrame b i y) +
          ∑ j : ι,
            e.localFrame_coeff I b j y (σ y) *
              e.localFrame_coeff I b k y
                ((cov (e.localFrame b j) y) (e.localFrame b i y))) x := by
    refine hderiv.add ?_
    exact ContMDiffAt.sum fun j _ => (hcoeff j).mul (hchristoffel j)
  exact hRhs.congr_of_eventuallyEq hEq
















omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem extDerivFun_apply_contMDiffAt_of_section
    {f : M -> Real} {X : (p : M) -> TangentSpace I p} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(Real, Real) ∞ f x₀)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
      (fun p : M => (⟨p, X p⟩ :
        TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun p : M => extDerivFun (I := I) f p (X p)) x₀ := by
  rw [contMDiffAt_infty]
  intro n
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let Xcoord : M -> E := fun p => e.continuousLinearMapAt Real p (X p)
  have hXcoord :
      ContMDiffAt I 𝓘(Real, E) (n : WithTop ℕ∞) Xcoord x₀ := by
    have hXTop :
        ContMDiffAt I 𝓘(Real, E) ∞
          (fun p : M => (e ⟨p, X p⟩).2) x₀ := by
      simpa [e] using
        (e.contMDiffAt_section_iff
          (s := X)
          (x₀ := x₀)
          (by simp [e])).mp hX
    refine (hXTop.of_le
      (by exact_mod_cast le_top : (n : WithTop ℕ∞) ≤ ∞)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds (by simp [e])] with p hp
    have hcoe : ⇑(e.linearMapAt Real p) = fun z => (e ⟨p, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := Real) hp
    simp [Xcoord, Bundle.Trivialization.continuousLinearMapAt_apply, hcoe]
  have hF :
      ContMDiffAt (I.prod I) 𝓘(Real, Real) ((n : WithTop ℕ∞) + 1)
        (fun q : M × M => f q.2) (x₀, x₀) := by
    exact (hf.comp (x₀, x₀) contMDiffAt_snd).of_le
      (by exact_mod_cast le_top : ((n : WithTop ℕ∞) + 1) ≤ ∞)
  have hApply :=
    ContMDiffAt.mfderiv_apply
      (I := I) (I' := 𝓘(Real, Real))
      (f := fun (_ : M) (p : M) => f p)
      (g := fun p : M => p)
      (g₁ := fun p : M => p)
      (g₂ := Xcoord)
      (x₀ := x₀)
      (m := (n : WithTop ℕ∞))
      hF contMDiffAt_id contMDiffAt_id hXcoord le_rfl
  refine hApply.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds (by simp [e])] with p hp
  have hp_src : p ∈ (chartAt H x₀).source := by
    simpa [e, TangentBundle.trivializationAt_baseSet] using hp
  have hf_src : f p ∈ (chartAt Real (f x₀)).source := by
    simp
  rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(Real, Real))
    (f := fun p : M => p) (g := f)
    (ϕ := fun p : M => mfderiv I 𝓘(Real, Real) f p)
    hp_src hf_src]
  have htarget :
      (tangentBundleCore 𝓘(Real, Real) Real).coordChange
        (achart Real (f p)) (achart Real (f x₀)) (f p) = (1 : Real →L[Real] Real) := by
    simp
  have hsource :
      (tangentBundleCore I M).coordChange (achart H x₀) (achart H p) p =
        e.symmL Real p := by
    simpa [e] using
      (TangentBundle.symmL_trivializationAt_eq_core
        (𝕜 := Real) (I := I) (b₀ := x₀) (b := p) hp_src).symm
  have hcancel :
      e.symmL Real p (Xcoord p) = X p := by
    exact e.symmL_continuousLinearMapAt (R := Real) hp (X p)
  rw [htarget, hsource]
  change (mfderiv I 𝓘(Real, Real) f p) (X p) =
    (mfderiv I 𝓘(Real, Real) f p) (e.symmL Real p (Xcoord p))
  rw [hcancel]







omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem extDerivFun_apply_contMDiffAt_of_section_one
    {f : M -> Real} {X : (p : M) -> TangentSpace I p} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(Real, Real) (2 : WithTop ℕ∞) f x₀)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
      (fun p : M => (⟨p, X p⟩ :
        TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun p : M => extDerivFun (I := I) f p (X p)) x₀ := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let Xcoord : M -> E := fun p => e.continuousLinearMapAt Real p (X p)
  have hXcoord :
      ContMDiffAt I 𝓘(Real, E) (1 : WithTop ℕ∞) Xcoord x₀ := by
    have hXtriv :
        ContMDiffAt I 𝓘(Real, E) (1 : WithTop ℕ∞)
          (fun p : M => (e ⟨p, X p⟩).2) x₀ := by
      simpa [e] using
        (e.contMDiffAt_section_iff
          (s := X)
          (x₀ := x₀)
          (by simp [e])).mp hX
    refine hXtriv.congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds (by simp [e])] with p hp
    have hcoe : ⇑(e.linearMapAt Real p) = fun z => (e ⟨p, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := Real) hp
    simp [Xcoord, Bundle.Trivialization.continuousLinearMapAt_apply, hcoe]
  have hF :
      ContMDiffAt (I.prod I) 𝓘(Real, Real) (2 : WithTop ℕ∞)
        (fun q : M × M => f q.2) (x₀, x₀) := by
    simpa using hf.comp (x₀, x₀) contMDiffAt_snd
  have hApply :=
    ContMDiffAt.mfderiv_apply
      (I := I) (I' := 𝓘(Real, Real))
      (f := fun (_ : M) (p : M) => f p)
      (g := fun p : M => p)
      (g₁ := fun p : M => p)
      (g₂ := Xcoord)
      (x₀ := x₀)
      (m := (1 : WithTop ℕ∞))
      hF contMDiffAt_id contMDiffAt_id hXcoord le_rfl
  refine hApply.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds (by simp [e])] with p hp
  have hp_src : p ∈ (chartAt H x₀).source := by
    simpa [e, TangentBundle.trivializationAt_baseSet] using hp
  have hf_src : f p ∈ (chartAt Real (f x₀)).source := by
    simp
  rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(Real, Real))
    (f := fun p : M => p) (g := f)
    (ϕ := fun p : M => mfderiv I 𝓘(Real, Real) f p)
    hp_src hf_src]
  have htarget :
      (tangentBundleCore 𝓘(Real, Real) Real).coordChange
        (achart Real (f p)) (achart Real (f x₀)) (f p) = (1 : Real →L[Real] Real) := by
    simp
  have hsource :
      (tangentBundleCore I M).coordChange (achart H x₀) (achart H p) p =
        e.symmL Real p := by
    simpa [e] using
      (TangentBundle.symmL_trivializationAt_eq_core
        (𝕜 := Real) (I := I) (b₀ := x₀) (b := p) hp_src).symm
  have hcancel :
      e.symmL Real p (Xcoord p) = X p := by
    exact e.symmL_continuousLinearMapAt (R := Real) hp (X p)
  rw [htarget, hsource]
  change (mfderiv I 𝓘(Real, Real) f p) (X p) =
    (mfderiv I 𝓘(Real, Real) f p) (e.symmL Real p (Xcoord p))
  rw [hcancel]

omit [CompleteSpace E] in
theorem localFrameCoeff_extDeriv_contMDiffAt
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x)
    (i k : ι) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        extDerivFun (I := I) ((LinearMap.piApply (e.localFrame_coeff I b k)) σ)
          y (e.localFrame b i y)) x := by
  have hcoeff :
      ContMDiffAt I 𝓘(Real, Real) ∞
        ((LinearMap.piApply (e.localFrame_coeff I b k)) σ) x :=
    contMDiffAt_localFrame_coeff
      (I := I) (V := TangentSpace I) (e := e) (b := b) (s := σ)
      (k := (∞ : WithTop ℕ∞)) hx hσ k
  have hframe :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (T% (e.localFrame b i)) x :=
    (e.isLocalFrameOn_localFrame_baseSet I ∞ b).contMDiffAt
      e.open_baseSet hx i
  exact extDerivFun_apply_contMDiffAt_of_section
    (I := I)
    (f := (LinearMap.piApply (e.localFrame_coeff I b k)) σ)
    (X := e.localFrame b i) hcoeff hframe



omit [CompleteSpace E] in
theorem localFrameCoeff_extDeriv_contMDiffAt_one
    {ι : Type*}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞) (T% σ) x)
    (i k : ι) :
    ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M =>
        extDerivFun (I := I) ((LinearMap.piApply (e.localFrame_coeff I b k)) σ)
          y (e.localFrame b i y)) x := by
  have hcoeff :
      ContMDiffAt I 𝓘(Real, Real) (2 : WithTop ℕ∞)
        ((LinearMap.piApply (e.localFrame_coeff I b k)) σ) x :=
    contMDiffAt_localFrame_coeff
      (I := I) (V := TangentSpace I) (e := e) (b := b) (s := σ)
      (k := (2 : WithTop ℕ∞)) hx hσ k
  have hframe :
      ContMDiffAt I (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (T% (e.localFrame b i)) x :=
    ((e.isLocalFrameOn_localFrame_baseSet I ∞ b).contMDiffAt
      e.open_baseSet hx i).of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  exact extDerivFun_apply_contMDiffAt_of_section_one
    (I := I)
    (f := (LinearMap.piApply (e.localFrame_coeff I b k)) σ)
    (X := e.localFrame b i) hcoeff hframe

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_contMDiffAt_of_section
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x)
    (i k : ι)
    (hchristoffel : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrame_coeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x := by
  refine covariantDerivative_localHomCoeff_contMDiffAt
    (I := I) cov e b hx hσdiff i k ?_ ?_ hchristoffel
  · exact localFrameCoeff_extDeriv_contMDiffAt (I := I) e b hx hσ i k
  · intro j
    exact contMDiffAt_localFrame_coeff
      (I := I) (V := TangentSpace I) (e := e) (b := b) (s := σ)
      (k := (∞ : WithTop ℕ∞)) hx hσ j



omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_contMDiffAt_of_section_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞) (T% σ) x)
    (i k : ι)
    (hchristoffel : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrame_coeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
      (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x := by
  refine covariantDerivative_localHomCoeff_contMDiffAt_one
    (I := I) cov e b hx hσdiff i k ?_ ?_ ?_
  · exact localFrameCoeff_extDeriv_contMDiffAt_one (I := I) e b hx hσ i k
  · intro j
    have hcoeff2 :
        ContMDiffAt I 𝓘(Real, Real) (2 : WithTop ℕ∞)
          (fun y : M => e.localFrame_coeff I b j y (σ y)) x :=
      contMDiffAt_localFrame_coeff
        (I := I) (V := TangentSpace I) (e := e) (b := b) (s := σ)
        (k := (2 : WithTop ℕ∞)) hx hσ j
    exact hcoeff2.of_le (by simp : (1 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞))
  · intro j
    exact (hchristoffel j).of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)

omit [CompleteSpace E] in
theorem covariantDerivative_homSection_contMDiffAt_of_coeff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x)
    (hchristoffel : ∀ i k j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrame_coeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun y : M =>
        (⟨y, cov σ y⟩ :
          TotalSpace (E →L[Real] E)
            (fun y : M => TangentSpace I y →L[Real] TangentSpace I y))) x := by
  classical
  let eHom := e.continuousLinearMap (RingHom.id Real) e
  let bHom := continuousLinearMap_homBasis (𝕜 := Real) b b
  have hhom : x ∈ eHom.baseSet := by
    simp [eHom, hx]
  refine
    (contMDiffAt_iff_localFrame_coeff (I := I) (e := eHom) bHom
      (s := fun y : M => cov σ y) (k := (∞ : WithTop ℕ∞)) hhom).mpr ?_
  rintro ⟨k, i⟩
  have hlocal :
      ContMDiffAt I 𝓘(Real, Real) ∞
        (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x :=
    covariantDerivative_localHomCoeff_contMDiffAt_of_section
      (I := I) cov e b hx hσdiff hσ i k (fun j => hchristoffel i k j)
  have heq :
      (fun y : M =>
          (eHom.localFrame_coeff I bHom (k, i) y) (cov σ y)) =ᶠ[𝓝 x]
        fun y : M => localHomCoeff (I := I) e b i k y (cov σ y) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact homLocalFrameCoeff_eq_localHomCoeff (I := I) e b hy (cov σ y) i k
  exact hlocal.congr_of_eventuallyEq heq



omit [CompleteSpace E] in
theorem covariantDerivative_homSection_contMDiffAt_of_coeff_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞) (T% σ) x)
    (hchristoffel : ∀ i k j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrame_coeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I (I.prod 𝓘(Real, E →L[Real] E)) (1 : WithTop ℕ∞)
      (fun y : M =>
        (⟨y, cov σ y⟩ :
          TotalSpace (E →L[Real] E)
            (fun y : M => TangentSpace I y →L[Real] TangentSpace I y))) x := by
  classical
  let eHom := e.continuousLinearMap (RingHom.id Real) e
  let bHom := continuousLinearMap_homBasis (𝕜 := Real) b b
  have hhom : x ∈ eHom.baseSet := by
    simp [eHom, hx]
  refine
    (contMDiffAt_iff_localFrame_coeff (I := I) (e := eHom) bHom
      (s := fun y : M => cov σ y) (k := (1 : WithTop ℕ∞)) hhom).mpr ?_
  rintro ⟨k, i⟩
  have hlocal :
      ContMDiffAt I 𝓘(Real, Real) (1 : WithTop ℕ∞)
        (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x :=
    covariantDerivative_localHomCoeff_contMDiffAt_of_section_one
      (I := I) cov e b hx hσdiff hσ i k (fun j => hchristoffel i k j)
  have heq :
      (fun y : M =>
          (eHom.localFrame_coeff I bHom (k, i) y) (cov σ y)) =ᶠ[𝓝 x]
        fun y : M => localHomCoeff (I := I) e b i k y (cov σ y) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact homLocalFrameCoeff_eq_localHomCoeff (I := I) e b hy (cov σ y) i k
  exact hlocal.congr_of_eventuallyEq heq


end DifferentialGeometry
