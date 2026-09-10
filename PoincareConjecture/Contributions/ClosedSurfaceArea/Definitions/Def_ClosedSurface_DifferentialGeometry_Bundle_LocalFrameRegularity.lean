import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_Section
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_SectionOperations
import Definitions.Def_ClosedSurface_DifferentialGeometry_Bundle_TangentSpace
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Basis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Bundle
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Comp
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Fiber
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_Multilinear_Tensor
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Basis
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Coordinates_Field
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Defs
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Derivation_NablaOnTensors
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_Field
import Definitions.Def_ClosedSurface_DifferentialGeometry_Tensor_RSTensor_NablaOnTensors_Connection_Smooth
import Definitions.Def_OpenGA_ImmersedMetric
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Data.Bundle
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.Perm.Option
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.VectorBundle.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

attribute [local instance] Fintype.ofFinite Classical.propDecidable

open Bundle

open DifferentialGeometry.Tensor0SBundle

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
        have hsum_raw := MDifferentiableAt.sum_section (s := t) (t := σ)
          (fun i _ => hσ i)
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
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x) (i k : ι) :
    e.localFrameCoeff I b k x
        ((cov σ x) (e.localFrame b i x)) =
      mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
        x (e.localFrame b i x) +
        ∑ j : ι,
          e.localFrameCoeff I b j x (σ x) *
            e.localFrameCoeff I b k x
              ((cov (e.localFrame b j) x) (e.localFrame b i x)) := by
  classical
  let frame : ι → (x : M) → TangentSpace I x := fun j => e.localFrame b j
  let coeff : ι → M → Real := fun j y => e.localFrameCoeff I b j y (σ y)
  let term : ι → (x : M) → TangentSpace I x := fun j => coeff j • frame j
  have hframe_diff (j : ι) : MDiffAt (T% (fun y => frame j y)) x := by
    simpa [frame] using
      ((e.isLocalFrameOn_localFrame_baseSet I ∞ b).contMDiffAt
        e.open_baseSet hx j).mdifferentiableAt (by simp)
  have hcoeff_diff (j : ι) :
      MDifferentiableAt I 𝓘(Real, Real) (coeff j) x := by
    simpa [coeff] using
      mdifferentiableAt_localFrameCoeff
        (I := I) (e := e) (b := b) hx hσ j
  have hterm_diff (j : ι) : MDiffAt (T% (fun y => term j y)) x := by
    exact (hcoeff_diff j).smul_section (hframe_diff j)
  have hsum_diff :
      MDiffAt (T% ((Finset.univ : Finset ι).sum term)) x := by
    simpa using
      MDifferentiableAt.sum_section
        (s := (Finset.univ : Finset ι)) (t := term) (fun j _ => hterm_diff j)
  have hσ_ev :
      σ =ᶠ[𝓝 x] fun y : M => ∑ j : ι, term j y := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    change σ y = ∑ j : ι,
      e.localFrameCoeff I b j y (σ y) • e.localFrame b j y
    exact e.eq_sum_localFrameCoeff_smul (I := I) (b := b) (s := σ) hy
  have hcov_congr :
      cov σ x = cov ((Finset.univ : Finset ι).sum term) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hσ hsum_diff
      (by simp) (by
        filter_upwards [hσ_ev] with y hy
        apply (tangentSpaceModelContinuousLinearEquiv (I := I) y).injective
        simpa only [Finset.sum_apply, map_sum,
          tangentSpaceModelContinuousLinearEquiv_apply] using hy)
  have hcov_sum :
      (cov σ x) (frame i x) =
        ∑ j : ι,
          (mvfderiv (I := I) (coeff j) x (frame i x) • frame j x +
            coeff j x • (cov (frame j) x) (frame i x)) := by
    calc
      (cov σ x) (frame i x)
          = (cov ((Finset.univ : Finset ι).sum term) x) (frame i x) := by
            rw [hcov_congr]
      _ = ∑ j : ι, (cov (term j) x) (frame i x) := by
            rw [covariantDerivative_finset_sum_tangent (I := I) cov
              (Finset.univ : Finset ι) term (frame i x) hterm_diff]
      _ = ∑ j : ι,
          (mvfderiv (I := I) (coeff j) x (frame i x) • frame j x +
            coeff j x • (cov (frame j) x) (frame i x)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            have hleib := congr($(cov.isCovariantDerivativeOnUniv.leibniz
              (σ := frame j) (g := coeff j) (x := x)
              (hframe_diff j) (hcoeff_diff j)) (frame i x))
            simpa [term, coeff, frame, add_comm] using hleib
  have hcoeff_frame (j l : ι) :
      e.localFrameCoeff I b l x (frame j x) = (if j = l then 1 else 0) := by
    rw [e.localFrameCoeff_apply_of_mem_baseSet b hx]
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
          e.localFrameCoeff I b k x
            (mvfderiv (I := I) (coeff j) x (frame i x) • frame j x)) =
        mvfderiv (I := I) (coeff k) x (frame i x) := by
    calc
      (∑ j : ι,
          e.localFrameCoeff I b k x
            (mvfderiv (I := I) (coeff j) x (frame i x) • frame j x))
          = ∑ j : ι,
              mvfderiv (I := I) (coeff j) x (frame i x) *
                e.localFrameCoeff I b k x (frame j x) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              simp
      _ = ∑ j : ι,
            mvfderiv (I := I) (coeff j) x (frame i x) *
              (if j = k then 1 else 0) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hcoeff_frame j k]
      _ = mvfderiv (I := I) (coeff k) x (frame i x) := by
              simp
  have hchristoffel_sum :
      (∑ j : ι,
          e.localFrameCoeff I b k x
            (coeff j x • (cov (frame j) x) (frame i x))) =
        ∑ j : ι,
          coeff j x *
            e.localFrameCoeff I b k x ((cov (frame j) x) (frame i x)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  rw [hderiv_sum, hchristoffel_sum]
  rfl

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
      e.localFrameCoeff I b k x (A (e.localFrame b i x)) := by
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
  simp only [Bundle.Trivialization.localFrameCoeff, IsLocalFrameOn.coeff, hx, ↓reduceDIte]
  rw [← hbasis]
  rw [((e.continuousLinearMap (RingHom.id Real) e).coe_linearMapAt_of_mem hhom)]
  change
    b.coord k (((e.continuousLinearMap (RingHom.id Real) e) ⟨x, A⟩).2 (b i)) =
      (e.basisAt b hx).coord k (A ((e.basisAt b hx) i))
  rw [Bundle.Trivialization.continuousLinearMap_apply]
  change b.coord k
      (e.continuousLinearMapAt Real x (A (e.symmL Real x (b i)))) =
    (e.basisAt b hx).coord k (A ((e.basisAt b hx) i))
  rw [e.symmL_apply hx (b i)]
  simp [Bundle.Trivialization.basisAt, Bundle.Trivialization.continuousLinearMapAt_apply,
    e.coe_linearMapAt_of_mem hx]

omit [CompleteSpace E] in
theorem homLocalFrameCoeff_eq_localHomCoeff
    {ι : Type*} [Finite ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {x : M} (hx : x ∈ e.baseSet)
    (A : TangentSpace I x →L[Real] TangentSpace I x) (i k : ι) :
    (e.continuousLinearMap (RingHom.id Real) e).localFrameCoeff I
        (continuousLinearMapHomBasis (𝕜 := Real) b b) (k, i) x A =
      localHomCoeff (I := I) e b i k x A := by
  let eHom := e.continuousLinearMap (RingHom.id Real) e
  let bHom := continuousLinearMapHomBasis (𝕜 := Real) b b
  have hhom : x ∈ eHom.baseSet := by
    simp [eHom, hx]
  classical
  let s : (y : M) → TangentSpace I y →L[Real] TangentSpace I y :=
    fun y => if h : x = y then h ▸ A else 0
  have hsx : s x = A := by
    simp [s]
  rw [← hsx]
  rw [eHom.localFrameCoeff_apply_of_mem_baseSet bHom hhom s (k, i)]
  simp only [eHom, bHom, hsx]
  simp [Bundle.Trivialization.basisAt, localHomCoeff, homModelCoeff,
    continuousLinearMap_homBasis_repr]
  simp only [((e.continuousLinearMap (RingHom.id Real) e).coe_linearMapAt_of_mem hhom)]

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_eq
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x) (i k : ι) :
    localHomCoeff (I := I) e b i k x (cov σ x) =
      mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
        x (e.localFrame b i x) +
        ∑ j : ι,
          e.localFrameCoeff I b j x (σ x) *
            e.localFrameCoeff I b k x
              ((cov (e.localFrame b j) x) (e.localFrame b i x)) := by
  rw [localHomCoeff_apply (I := I) e b hx (cov σ x) i k]
  exact covariantDerivative_localFrame_coeff_eq (I := I) cov e b hx hσ i k

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_eventuallyEq
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y) (i k : ι) :
    (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) =ᶠ[𝓝 x]
      fun y : M =>
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y) +
          ∑ j : ι,
            e.localFrameCoeff I b j y (σ y) *
              e.localFrameCoeff I b k y
                ((cov (e.localFrame b j) y) (e.localFrame b i y)) := by
  filter_upwards [e.open_baseSet.mem_nhds hx, hσ] with y hy hσy
  exact covariantDerivative_localHomCoeff_eq (I := I) cov e b hy hσy i k

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_contMDiffAt
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet) (hσ : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (i k : ι)
    (hderiv : ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y)) x)
    (hcoeff : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => e.localFrameCoeff I b j y (σ y)) x)
    (hchristoffel : ∀ j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x := by
  have hEq :=
    covariantDerivative_localHomCoeff_eventuallyEq (I := I) cov e b hx hσ i k
  have hRhs : ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y) +
          ∑ j : ι,
            e.localFrameCoeff I b j y (σ y) *
              e.localFrameCoeff I b k y
                ((cov (e.localFrame b j) y) (e.localFrame b i y))) x := by
    refine hderiv.add ?_
    exact ContMDiffAt.sum fun j _ => (hcoeff j).mul (hchristoffel j)
  exact hRhs.congr_of_eventuallyEq hEq

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem mvfderiv_apply_contMDiffAt_of_section
    {f : M -> Real} {X : (p : M) -> TangentSpace I p} {x₀ : M}
    (hf : ContMDiffAt I 𝓘(Real, Real) ∞ f x₀)
    (hX : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
      (fun p : M => (⟨p, X p⟩ :
        TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun p : M => mvfderiv (I := I) f p (X p)) x₀ := by
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
    change e.continuousLinearMapAt Real p (X p) = (e ⟨p, X p⟩).2
    exact congrFun hcoe (X p)
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
    rw [chartAt_self_eq]
    exact Set.mem_univ _
  rw [inTangentCoordinates_eq (I := I) (I' := 𝓘(Real, Real))
    (f := fun p : M => p) (g := f)
    (ϕ := fun p : M => mfderiv I 𝓘(Real, Real) f p)
    hp_src hf_src]
  have htarget :
      (tangentBundleCore 𝓘(Real, Real) Real).coordChange
        (achart Real (f p)) (achart Real (f x₀)) (f p) = (1 : Real →L[Real] Real) := by
    simp
  have hsource_raw :=
    (TangentBundle.symmL_trivializationAt_eq_core
      (𝕜 := Real) (I := I) (b₀ := x₀) (b := p) hp_src).symm
  have hcancel :
      e.symmL Real p (Xcoord p) = X p := by
    exact e.symmL_continuousLinearMapAt (R := Real) hp (X p)
  rw [htarget, hsource_raw]
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
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b k)) σ)
          y (e.localFrame b i y)) x := by
  have hcoeff :
      ContMDiffAt I 𝓘(Real, Real) ∞
        ((LinearMap.piApply (e.localFrameCoeff I b k)) σ) x :=
    contMDiffAt_localFrameCoeff
      (I := I) (V := TangentSpace I) (e := e) (b := b) (s := σ)
      (k := (∞ : WithTop ℕ∞)) hx hσ k
  have hframe :
      ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (T% (e.localFrame b i)) x :=
    (e.isLocalFrameOn_localFrame_baseSet I ∞ b).contMDiffAt
      e.open_baseSet hx i
  exact mvfderiv_apply_contMDiffAt_of_section
    (I := I)
    (f := (LinearMap.piApply (e.localFrameCoeff I b k)) σ)
    (X := e.localFrame b i) hcoeff hframe

omit [CompleteSpace E] in
theorem covariantDerivative_localHomCoeff_contMDiffAt_of_section
    {ι : Type*} [Finite ι]
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
        e.localFrameCoeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x := by
  refine covariantDerivative_localHomCoeff_contMDiffAt
    (I := I) cov e b hx hσdiff i k ?_ ?_ hchristoffel
  · exact localFrameCoeff_extDeriv_contMDiffAt (I := I) e b hx hσ i k
  · intro j
    exact contMDiffAt_localFrameCoeff
      (I := I) (V := TangentSpace I) (e := e) (b := b) (s := σ)
      (k := (∞ : WithTop ℕ∞)) hx hσ j

omit [CompleteSpace E] in
theorem covariantDerivative_homSection_contMDiffAt_of_coeff
    {ι : Type*} [Finite ι]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι Real E)
    {σ : (x : M) → TangentSpace I x} {x : M}
    (hx : x ∈ e.baseSet)
    (hσdiff : ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y)
    (hσ : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞ (T% σ) x)
    (hchristoffel : ∀ i k j : ι, ContMDiffAt I 𝓘(Real, Real) ∞
      (fun y : M =>
        e.localFrameCoeff I b k y
          ((cov (e.localFrame b j) y) (e.localFrame b i y))) x) :
    ContMDiffAt I (I.prod 𝓘(Real, E →L[Real] E)) ∞
      (fun y : M =>
        (⟨y, cov σ y⟩ :
          TotalSpace (E →L[Real] E)
            (fun y : M => TangentSpace I y →L[Real] TangentSpace I y))) x := by
  classical
  let eHom := e.continuousLinearMap (RingHom.id Real) e
  let bHom := continuousLinearMapHomBasis (𝕜 := Real) b b
  have hhom : x ∈ eHom.baseSet := by
    simp [eHom, hx]
  refine
    (contMDiffAt_iff_localFrameCoeff (I := I) (e := eHom) bHom
      (s := fun y : M => cov σ y) (k := (∞ : WithTop ℕ∞)) hhom).mpr ?_
  rintro ⟨k, i⟩
  have hlocal :
      ContMDiffAt I 𝓘(Real, Real) ∞
        (fun y : M => localHomCoeff (I := I) e b i k y (cov σ y)) x :=
    covariantDerivative_localHomCoeff_contMDiffAt_of_section
      (I := I) cov e b hx hσdiff hσ i k (fun j => hchristoffel i k j)
  have heq :
      (fun y : M =>
          (eHom.localFrameCoeff I bHom (k, i) y) (cov σ y)) =ᶠ[𝓝 x]
        fun y : M => localHomCoeff (I := I) e b i k y (cov σ y) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact homLocalFrameCoeff_eq_localHomCoeff (I := I) e b hy (cov σ y) i k
  exact hlocal.congr_of_eventuallyEq heq

end DifferentialGeometry

end
