import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.RawDefs.MCovariant
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.RawDefs.Bundled
import DifferentialGeometry.Tensor.RSTensor.Basis
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Multilinear.Bundle
import DifferentialGeometry.Tensor.Alternating.Comp
import DifferentialGeometry.Tensor.Multilinear.Comp
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import DifferentialGeometry.Tensor.Auxiliary.LinearIsometryContDiff
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.ModelMixed
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase




namespace Tensor0SBundle

open Bundle Set TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private theorem fderivWithin_eq_sum_basis_coord
    {F : E -> E} {u : Set E} {y Xy : E}
    (hF : DifferentiableWithinAt 𝕜 F u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    fderivWithin 𝕜 F u y Xy =
      ∑ i : Fin (Module.finrank 𝕜 E),
        fderivWithin 𝕜
          (fun z : E => (Module.finBasis 𝕜 E).coord i (F z)) u y Xy •
          (Module.finBasis 𝕜 E) i := by
  classical
  let b : Module.Basis (Fin (Module.finrank 𝕜 E)) 𝕜 E := Module.finBasis 𝕜 E
  apply b.ext_elem
  intro i
  let L : E →L[𝕜] 𝕜 := LinearMap.toContinuousLinearMap (b.coord i)
  have hcomp :
      fderivWithin 𝕜 (fun z : E => L (F z)) u y =
        L.comp (fderivWithin 𝕜 F u y) := by
    have hlin :
        DifferentiableAt 𝕜 (fun w : E => L w) (F y) :=
      L.differentiableAt
    have hcomp0 :=
      (fderivWithin_comp (x := y) (f := F)
        (g := fun w : E => L w) (s := u) (t := Set.univ)
        (by simpa using hlin.differentiableWithinAt)
        hF (by intro z hz; simp) hu)
    rw [L.fderivWithin (s := Set.univ) (x := F y) uniqueDiffWithinAt_univ] at hcomp0
    simpa [L, b, Function.comp_def] using hcomp0
  have hcoord' :
      b.coord i ((fderivWithin 𝕜 F u y) Xy) =
        fderivWithin 𝕜 (fun z : E => b.coord i (F z)) u y Xy := by
    change L ((fderivWithin 𝕜 F u y) Xy) =
      fderivWithin 𝕜 (fun z : E => L (F z)) u y Xy
    rw [hcomp]
    simp [L, LinearMap.coe_toContinuousLinearMap']
  have hcoord :
      b.repr ((fderivWithin 𝕜 F u y) Xy) i =
        fderivWithin 𝕜 (fun z : E => b.coord i (F z)) u y Xy := by
    simpa [Module.Basis.coord_apply] using hcoord'
  rw [hcoord]
  change (fderivWithin 𝕜 (fun z : E => b.coord i (F z)) u y) Xy =
    b.coord i
      (∑ j : Fin (Module.finrank 𝕜 E),
        (fderivWithin 𝕜
          (fun z : E => (Module.finBasis 𝕜 E).coord j (F z)) u y) Xy •
          (Module.finBasis 𝕜 E) j)
  rw [map_sum]
  simp only [b, Module.Basis.coord_apply, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have hrepr :
        ((Module.finBasis 𝕜 E).repr ((Module.finBasis 𝕜 E) j)) i = 0 := by
      have hji : i ≠ j := fun h => hj h.symm
      rw [(Module.finBasis 𝕜 E).repr_self j]
      exact Finsupp.single_eq_of_ne hji
    rw [hrepr]
    simp
  · intro hi
    simp at hi

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
private theorem fderivWithin_chart_scalar_eq_extDerivFun
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (φ : E -> 𝕜) (f : M -> 𝕜)
    (hf : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x₀)
    (heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f) :
    fderivWithin 𝕜 φ (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) =
      extDerivFun (I := I) f x₀ (X x₀) := by
  let z₀ : E := extChartAt I x₀ x₀
  have hzRange : z₀ ∈ Set.range I :=
    extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
  have hX :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) z₀ =
        X x₀ := by
    simp only [z₀, VectorField.mpullbackWithin_apply]
    rw [extChartAt_to_inv]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x₀) (X x₀)
  have hfd :
      fderivWithin 𝕜 φ (Set.range I) z₀ =
        fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f)
          (Set.range I) z₀ :=
    heq.fderivWithin_eq_of_mem hzRange
  change
    fderivWithin 𝕜 φ (Set.range I) z₀
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) z₀) =
      (mfderiv I 𝓘(𝕜, 𝕜) f x₀) (X x₀)
  rw [hX, hf.mfderiv, hfd]
  rfl

private theorem tangentFieldModelInChart_fderivWithin_eq_sum_extDerivFun_coord
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hVmodel :
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
              (extChartAt I x₀ p))) x₀) :
    fderivWithin 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) =
      ∑ i : Fin (Module.finrank 𝕜 E),
        extDerivFun (I := I)
          (fun p : M =>
            (Module.finBasis 𝕜 E).coord i
              (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                (extChartAt I x₀ p))) x₀ (X x₀) •
          (Module.finBasis 𝕜 E) i := by
  classical
  let F : E -> E := tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
  let b : Module.Basis (Fin (Module.finrank 𝕜 E)) 𝕜 E := Module.finBasis 𝕜 E
  have hbasis := fderivWithin_eq_sum_basis_coord
    (F := F) (u := Set.range I) (y := extChartAt I x₀ x₀)
    (Xy := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I) (extChartAt I x₀ x₀))
    hVmodel (I.uniqueDiffOn (extChartAt I x₀ x₀)
      (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)))
  rw [hbasis]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  let f : M -> 𝕜 := fun p : M => b.coord i (F (extChartAt I x₀ p))
  let φ : E -> 𝕜 := fun y : E => b.coord i (F y)
  have hφ : DifferentiableWithinAt 𝕜 φ (Set.range I) (extChartAt I x₀ x₀) := by
    exact (LinearMap.toContinuousLinearMap (b.coord i)).differentiableAt.comp_differentiableWithinAt
      (x := extChartAt I x₀ x₀) hVmodel
  have heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    have hright : extChartAt I x₀ ((extChartAt I x₀).symm y) = y :=
      (extChartAt I x₀).right_inv hy
    simp only [φ, f, writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
    change b.coord i (F y) =
      b.coord i (F (extChartAt I x₀ ((extChartAt I x₀).symm y)))
    rw [hright]
  exact fderivWithin_chart_scalar_eq_extDerivFun
    (I := I) X x₀ φ f (hcoord i) heq

theorem covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : MDiffAt (T% V) x₀)
    (hVmodel :
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
              (extChartAt I x₀ p))) x₀) :
    tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
        (fun p : M => (cov V p) (X p)) (extChartAt I x₀ x₀) =
      fderivWithin 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) +
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀
        (extChartAt I x₀ x₀)
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀)) := by
  classical
  let b := Module.finBasis 𝕜 E
  let zfun : Fin (Module.finrank 𝕜 E) -> M -> 𝕜 :=
    fun i p =>
      b.coord i
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ p))
  have hsum := covariantDerivative_modelInChart_center_eq_sum
    (𝕜 := 𝕜) (I := I) cov (fun x => X x) V x₀ hV hcoord
  have hderiv :=
    tangentFieldModelInChart_fderivWithin_eq_sum_extDerivFun_coord
      (I := I) X V x₀ hVmodel hcoord
  calc
    tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
        (fun p : M => (cov V p) (X p)) (extChartAt I x₀ x₀)
        =
      (∑ i : Fin (Module.finrank 𝕜 E),
        extDerivFun (I := I) (zfun i) x₀ (X x₀) • b i) +
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀
        (extChartAt I x₀ x₀)
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀)) := by
          simpa [b, zfun] using hsum
    _ =
      fderivWithin 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) +
      connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀
        (extChartAt I x₀ x₀)
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀)) := by
          rw [hderiv]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
private theorem tangentFieldModelInChart_center_symmL
    (V : (x : M) -> TangentSpace I x) (x₀ : M) :
    (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
          (extChartAt I x₀ x₀)) =
      V x₀ := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  unfold tangentFieldModelInChart
  change e.symmL 𝕜 x₀
      (e.continuousLinearMapAt 𝕜 ((extChartAt I x₀).symm (extChartAt I x₀ x₀))
        (V ((extChartAt I x₀).symm (extChartAt I x₀ x₀)))) =
    V x₀
  rw [extChartAt_to_inv]
  exact e.symmL_continuousLinearMapAt
    (R := 𝕜) (FiberBundle.mem_baseSet_trivializationAt' x₀) (V x₀)

omit [CompleteSpace 𝕜] in
private theorem tensor0SModelInChart_apply_modelSlots_center {s : ℕ}
    (A : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M) :
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ A (extChartAt I x₀ x₀)
        (fun a : Fin s =>
          tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
            (extChartAt I x₀ x₀)) =
      A x₀ (fun a : Fin s => V a x₀) := by
  rw [tensor0SModelInChart_apply]
  rw [extChartAt_to_inv]
  congr
  funext a
  exact tangentFieldModelInChart_center_symmL (I := I) (V a) x₀

omit [CompleteSpace 𝕜] in
private theorem tensor0SModelInChart_apply_update_modelSlot_center {s : ℕ}
    (A : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s x)
    (V : Fin s -> (x : M) -> TangentSpace I x)
    (W : (x : M) -> TangentSpace I x) (x₀ : M) (a : Fin s) :
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s x₀ A (extChartAt I x₀ x₀)
        (Function.update
          (fun b : Fin s =>
            tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V b)
              (extChartAt I x₀ x₀))
          a
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ W
            (extChartAt I x₀ x₀))) =
      A x₀ (Function.update (fun b : Fin s => V b x₀) a (W x₀)) := by
  rw [tensor0SModelInChart_apply]
  rw [extChartAt_to_inv]
  congr
  funext b
  by_cases hb : b = a
  · subst hb
    simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
      ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe,
      Function.comp_apply, Function.update_self, Trivialization.symmL_apply]
    exact tangentFieldModelInChart_center_symmL (I := I) W x₀
  · simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
      ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe,
      Function.comp_apply, Function.update_of_ne hb, Trivialization.symmL_apply]
    exact tangentFieldModelInChart_center_symmL (I := I) (V b) x₀

omit [CompleteSpace 𝕜] in
private theorem fderivWithin_tensor0S_eval_modelSlots_center_eq_extDerivFun {s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => α p (fun a : Fin s => V a p)) x₀) :
    fderivWithin 𝕜
        (fun y : E =>
          tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) s x₀ (fun x => α x) y
            (fun a : Fin s =>
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y))
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀) := by
  let φ : E -> 𝕜 :=
    fun y : E =>
      tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) s x₀ (fun x => α x) y
        (fun a : Fin s =>
          tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y)
  let f : M -> 𝕜 := fun p : M => α p (fun a : Fin s => V a p)
  have heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    have hleft : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    have hbase :
        (extChartAt I x₀).symm y ∈
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      simpa [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hleft
    simp only [φ, f, writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
    rw [tensor0SModelInChart_apply]
    congr
    funext a
    unfold tangentFieldModelInChart
    exact (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hbase (V a ((extChartAt I x₀).symm y))
  exact fderivWithin_chart_scalar_eq_extDerivFun
    (I := I) X x₀ φ f hpair heq

omit [CompleteSpace 𝕜] in
private theorem fderivWithin_localTensor0S_eval_modelSlots_center_eq_extDerivFun {s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => β p (fun a : Fin s => V a p)) x₀) :
    fderivWithin 𝕜
        (fun y : E =>
          tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) s x₀ β y
            (fun a : Fin s =>
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y))
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) =
      extDerivFun (I := I) (fun p : M => β p (fun a : Fin s => V a p))
        x₀ (X x₀) := by
  let φ : E -> 𝕜 :=
    fun y : E =>
      tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) s x₀ β y
        (fun a : Fin s =>
          tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y)
  let f : M -> 𝕜 := fun p : M => β p (fun a : Fin s => V a p)
  have heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    have hleft : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    have hbase :
        (extChartAt I x₀).symm y ∈
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      simpa [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hleft
    simp only [φ, f, writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
    rw [tensor0SModelInChart_apply]
    congr
    funext a
    unfold tangentFieldModelInChart
    exact (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hbase (V a ((extChartAt I x₀).symm y))
  exact fderivWithin_chart_scalar_eq_extDerivFun
    (I := I) X x₀ φ f hpair heq

set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace 𝕜] in
private theorem fderivWithin_tensorRS_eval_modelSlots_center_eq_extDerivFun {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀) :
    fderivWithin 𝕜
        (fun y : E =>
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
              (M := M) r s x₀ (fun x => T x) y
            (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
              (M := M) r x₀ β y))
            (fun a : Fin s =>
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y))
        (Set.range I) (extChartAt I x₀ x₀)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) (extChartAt I x₀ x₀)) =
      extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
        x₀ (X x₀) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  letI : NormedSpace 𝕜 (Tensor0SModel r 𝕜 E) := inferInstance
  let φ : E -> 𝕜 :=
    fun y : E =>
      (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r s x₀ (fun x => T x) y
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r x₀ β y))
        (fun a : Fin s =>
          tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a) y)
  let f : M -> 𝕜 := fun p : M => (T p (β p)) (fun a : Fin s => V a p)
  have heq :
      φ =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    have hleft : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    have hbase :
        (extChartAt I x₀).symm y ∈
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      simpa [TangentBundle.trivializationAt_baseSet, extChartAt_source] using hleft
    simp only [φ, f, writtenInExtChartAt, Function.comp_apply, ext_chart_model_space_apply]
    unfold tensorRSModelInChart tensorRSModelAt
    rw [TensorRSSpace.trivializationAt_apply]
    · congr 2
      · unfold tensor0SModelInChart tensor0SModelAt
        let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀
        let p := (extChartAt I x₀).symm y
        have hbaseβ : p ∈ eβ.baseSet := hbase
        change eβ.symmL 𝕜 p ((eβ ⟨p, β p⟩).2) = β p
        have hcoord : (eβ ⟨p, β p⟩).2 = eβ.continuousLinearMapAt 𝕜 p (β p) := by
          rw [Bundle.Trivialization.continuousLinearMapAt_apply]
          rw [eβ.coe_linearMapAt_of_mem (R := 𝕜) hbaseβ]
        rw [hcoord]
        exact eβ.symmL_continuousLinearMapAt (R := 𝕜) hbaseβ (β p)
      · funext a
        unfold tangentFieldModelInChart
        exact (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL_continuousLinearMapAt
          (R := 𝕜) hbase (V a ((extChartAt I x₀).symm y))
    · exact hbase
  exact fderivWithin_chart_scalar_eq_extDerivFun
    (I := I) X x₀ φ f hpair heq

noncomputable def localCovariantDerivTensor0SAt (r : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (x₀ : M) : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r x₀ := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  exact (trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀).symm x₀
    (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
      (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (fun x => X x) (Set.range I))
      (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))

set_option backward.isDefEq.respectTransparency false in
theorem localCovariantDerivTensor0SAt_eval_moving_raw {r : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin r -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => β p (fun a : Fin r => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin r, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin r,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin r, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (localCovariantDerivTensor0SAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
      (fun a : Fin r => V a x₀) =
      extDerivFun (I := I) (fun p : M => β p (fun a : Fin r => V a p))
        x₀ (X x₀) -
        ∑ a : Fin r,
          β x₀
            (Function.update (fun b : Fin r => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  classical
  let y₀ : E := extChartAt I x₀ x₀
  let Xmodel : E :=
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I) y₀
  let βm : E -> Tensor0SModel (𝕜 := 𝕜) (E := E) r :=
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x₀ β
  let Vm : Fin r -> E -> E :=
    fun a => tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
  let Γ : E →L[𝕜] E :=
    connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ y₀
  let slots : Fin r -> E := fun a => Vm a y₀
  have hprod :=
    fderivWithin_tensor0SModel_eval_slots
      (𝕜 := 𝕜) (E := E) (s := r) βm Vm (Set.range I) y₀ Xmodel
      hβmodel hVmodel
      (I.uniqueDiffOn y₀
        (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)))
  have hpair_deriv :
      fderivWithin 𝕜 (fun y : E => βm y (fun a : Fin r => Vm a y))
          (Set.range I) y₀ Xmodel =
        extDerivFun (I := I) (fun p : M => β p (fun a : Fin r => V a p))
          x₀ (X x₀) := by
    simpa [βm, Vm, Xmodel, y₀] using
      fderivWithin_localTensor0S_eval_modelSlots_center_eq_extDerivFun
        (I := I) X β V x₀ hpair
  have hcov_model : ∀ a : Fin r,
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
          (fun p : M => (cov (V a) p) (X p)) y₀ =
        fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a) := by
    intro a
    simpa [Vm, Xmodel, Γ, slots, y₀] using
      covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
        (I := I) cov X (V a) x₀ (hV a) (hVmodel a) (hcoord a)
  have hslots_center :
      (fun a : Fin r =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
          (slots a)) =
        fun a : Fin r => V a x₀ := by
    funext a
    simpa [slots, Vm] using tangentFieldModelInChart_center_symmL (I := I) (V a) x₀
  have hleft_model :
      (localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
        (fun a : Fin r => V a x₀) =
      (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I))
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        βm (Set.range I) y₀) slots := by
    let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀
    let Mβ : Tensor0SModel r 𝕜 E :=
      covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I))
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        βm (Set.range I) y₀
    have hcoordEval :
        ((eβ ⟨x₀, localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀⟩).2)
            slots =
          (localCovariantDerivTensor0SAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
            (fun a : Fin r => V a x₀) := by
      have h := Tensor0SSpace.trivializationAt_apply
        (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x₀) r
        (FiberBundle.mem_baseSet_trivializationAt' x₀)
        (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
        slots
      rw [hslots_center] at h
      exact h
    have hmodel :
        (eβ ⟨x₀, localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀⟩).2 =
          Mβ := by
      unfold localCovariantDerivTensor0SAt
      change (eβ ⟨x₀, eβ.symm x₀ Mβ⟩).2 = Mβ
      rw [eβ.apply_mk_symm
        (mem_baseSet_trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀)]
    calc
      (localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
        (fun a : Fin r => V a x₀)
          = ((eβ ⟨x₀, localCovariantDerivTensor0SAt
              (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀⟩).2)
              slots := hcoordEval.symm
      _ = Mβ slots := by rw [hmodel]
  have hcorr_sum :
      ∑ a : Fin r,
        βm y₀
          (Function.update slots a
            (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a))) =
      ∑ a : Fin r,
        β x₀
          (Function.update (fun b : Fin r => V b x₀) a
            ((cov (V a) x₀) (X x₀))) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcov_model a]
    exact tensor0SModelInChart_apply_update_modelSlot_center
      (I := I) β V (fun p : M => (cov (V a) p) (X p)) x₀ a
  calc
    (localCovariantDerivTensor0SAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)
      (fun a : Fin r => V a x₀)
        =
      (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I))
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        βm (Set.range I) y₀) slots := hleft_model
    _ =
      fderivWithin 𝕜 βm (Set.range I) y₀ Xmodel slots -
        ∑ a : Fin r, βm y₀ (Function.update slots a (Γ (slots a))) := by
          simp [covariantDeriv_tensor0SModelWithin_apply_slots, βm, Xmodel, Γ, slots, y₀]
    _ =
      extDerivFun (I := I) (fun p : M => β p (fun a : Fin r => V a p))
          x₀ (X x₀) -
        ∑ a : Fin r,
          βm y₀
            (Function.update slots a
              (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a))) := by
          rw [← hpair_deriv]
          rw [hprod]
          simp_rw [(βm y₀).map_update_add]
          rw [Finset.sum_add_distrib]
          abel
    _ =
      extDerivFun (I := I) (fun p : M => β p (fun a : Fin r => V a p))
          x₀ (X x₀) -
        ∑ a : Fin r,
          β x₀
            (Function.update (fun b : Fin r => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
          rw [hcorr_sum]

set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace 𝕜] in
private theorem tensorRSModelInChart_apply_modelSlots_center {r s : ℕ}
    (A : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r s x)
    (βm : Tensor0SModel r 𝕜 E) (slots : Fin s -> E) (x₀ : M) :
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
    (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s x₀ A (extChartAt I x₀ x₀) βm) slots =
      (A x₀
        ((trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x₀ βm))
        (fun a : Fin s =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
            (slots a)) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  rw [tensorRSModelInChart, extChartAt_to_inv]
  exact TensorRSSpace.trivializationAt_apply
    (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x₀) r s
    (FiberBundle.mem_baseSet_trivializationAt' x₀) (A x₀) βm slots

set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace 𝕜] in
private theorem tensorRSModelInChart_apply_update_modelOutputSlot_center {r s : ℕ}
    (A : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r s x)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x)
    (W : (x : M) -> TangentSpace I x) (x₀ : M) (a : Fin s) :
    (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s x₀ A (extChartAt I x₀ x₀)
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r x₀ β (extChartAt I x₀ x₀)))
        (Function.update
          (fun b : Fin s =>
            tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V b)
              (extChartAt I x₀ x₀))
          a
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ W
            (extChartAt I x₀ x₀))) =
      (A x₀ (β x₀)) (Function.update (fun b : Fin s => V b x₀) a (W x₀)) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  rw [tensorRSModelInChart_apply_modelSlots_center]
  have hβ :
      (trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x₀
          (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) r x₀ β (extChartAt I x₀ x₀)) =
        β x₀ := by
    unfold tensor0SModelInChart tensor0SModelAt
    rw [extChartAt_to_inv]
    let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
      (fun x => Tensor0SSpace r I x) x₀
    change eβ.symmL 𝕜 x₀ ((eβ ⟨x₀, β x₀⟩).2) = β x₀
    have hcoord : (eβ ⟨x₀, β x₀⟩).2 = eβ.continuousLinearMapAt 𝕜 x₀ (β x₀) := by
      rw [Bundle.Trivialization.continuousLinearMapAt_apply]
      rw [eβ.coe_linearMapAt_of_mem (R := 𝕜)
        (FiberBundle.mem_baseSet_trivializationAt' x₀)]
    rw [hcoord]
    exact eβ.symmL_continuousLinearMapAt (R := 𝕜)
      (FiberBundle.mem_baseSet_trivializationAt' x₀) (β x₀)
  have hslots :
      (fun b : Fin s =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
          ((Function.update
            (fun b : Fin s =>
              tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V b)
                (extChartAt I x₀ x₀))
            a
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ W
              (extChartAt I x₀ x₀))) b)) =
        Function.update (fun b : Fin s => V b x₀) a (W x₀) := by
    funext b
    by_cases hb : b = a
    · subst hb
      simp only [Function.update_self]
      exact tangentFieldModelInChart_center_symmL (I := I) W x₀
    · simp only [Function.update_of_ne hb]
      exact tangentFieldModelInChart_center_symmL (I := I) (V b) x₀
  rw [hβ, hslots]

theorem localCovDeriv0S_sub {r : ℕ}
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin r -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => β p (fun a : Fin r => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin r, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin r,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin r, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀
        (fun a : Fin r => V a x₀) -
      localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov' X β x₀
        (fun a : Fin r => V a x₀)) =
      -∑ a : Fin r,
        β x₀
          (Function.update (fun b : Fin r => V b x₀) a
            (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀))) := by
  classical
  let slots : Fin r -> TangentSpace I x₀ := fun a => V a x₀
  have hcov := localCovariantDerivTensor0SAt_eval_moving_raw
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    cov X β V x₀ hpair hβmodel hV hVmodel hcoord
  have hcov' := localCovariantDerivTensor0SAt_eval_moving_raw
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    cov' X β V x₀ hpair hβmodel hV hVmodel hcoord
  have hdiff (a : Fin r) :
      β x₀
          (Function.update slots a ((cov (V a) x₀) (X x₀))) -
        β x₀
          (Function.update slots a ((cov' (V a) x₀) (X x₀))) =
        β x₀
          (Function.update slots a
            (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀))) := by
    have hconn :
        ((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀) =
          ((cov (V a) x₀) (X x₀)) - ((cov' (V a) x₀) (X x₀)) := by
      have h :=
        IsCovariantDerivativeOn.difference_apply
          (hcov := cov.isCovariantDerivativeOnUniv)
          (hcov' := cov'.isCovariantDerivativeOnUniv)
          (σ := V a) (x := x₀) (hx := by trivial) (hV a)
      exact congrArg (fun L : TangentSpace I x₀ →L[𝕜] TangentSpace I x₀ => L (X x₀)) h
    rw [hconn]
    exact ((β x₀).map_update_sub slots a
      ((cov (V a) x₀) (X x₀))
      ((cov' (V a) x₀) (X x₀))).symm
  let D : 𝕜 :=
    extDerivFun (I := I) (fun p : M => β p (fun a : Fin r => V a p))
      x₀ (X x₀)
  let Scov : 𝕜 :=
    ∑ a : Fin r, β x₀ (Function.update slots a ((cov (V a) x₀) (X x₀)))
  let Scov' : 𝕜 :=
    ∑ a : Fin r, β x₀ (Function.update slots a ((cov' (V a) x₀) (X x₀)))
  let Sdiff : 𝕜 :=
    ∑ a : Fin r,
      β x₀
        (Function.update slots a
          (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀)))
  have hsum : Scov - Scov' = Sdiff := by
    dsimp [Scov, Scov', Sdiff]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact hdiff a
  change
      ((localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀) slots -
        (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov' X β x₀) slots) =
        -Sdiff
  rw [hcov, hcov']
  change (D - Scov) - (D - Scov') = -Sdiff
  rw [← hsum]
  abel

set_option backward.isDefEq.respectTransparency false in
theorem nablaRSFun_eval_moving_raw {r s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T x₀) (β x₀) (fun a : Fin s => V a x₀) =
      extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
        x₀ (X x₀) -
        (T x₀ (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀) -
        ∑ a : Fin s,
          (T x₀ (β x₀))
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  classical
  let y₀ : E := extChartAt I x₀ x₀
  let Xmodel : E :=
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I) y₀
  let Tm : E -> TensorRSModel r s 𝕜 E :=
    tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r s x₀ (fun x => T x)
  let βm : E -> Tensor0SModel r 𝕜 E :=
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x₀ β
  let Vm : Fin s -> E -> E :=
    fun a => tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
  let Γ : E →L[𝕜] E :=
    connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ y₀
  let slots : Fin s -> E := fun a => Vm a y₀
  have hTdiff : DifferentiableWithinAt 𝕜 Tm (Set.range I) y₀ := by
    have hcd := (T.contMDiff x₀)
    rw [contMDiffAt_section] at hcd
    have hsymm :
        ContMDiffWithinAt 𝓘(𝕜, E) I (∞ : WithTop ℕ∞)
          (extChartAt I x₀).symm (Set.range I) y₀ := by
      simpa [y₀] using
        contMDiffWithinAt_extChartAt_symm_range_self
          (I := I) (n := (∞ : WithTop ℕ∞)) x₀
    have hmodel_center :
        ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) (∞ : WithTop ℕ∞)
          (fun x : M => tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ x (T x))
          ((extChartAt I x₀).symm y₀) := by
      simpa [tensorRSModelAt, y₀, extChartAt_to_inv] using hcd
    have hcomp := ContMDiffAt.comp_contMDiffWithinAt
      (I := 𝓘(𝕜, E)) (I' := I)
      (I'' := 𝓘(𝕜, TensorRSModel r s 𝕜 E))
      (x := y₀) hmodel_center hsymm
    have hdiff := hcomp.contDiffWithinAt.differentiableWithinAt (by simp)
    simpa [Tm, tensorRSModelInChart, y₀] using hdiff
  have hprod := covariantDeriv_tensorRSModelWithin_eval_derivation
    (𝕜 := 𝕜) (E := E) (r := r) (s := s)
    Tm βm Vm
    (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I))
    (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
    (Set.range I) y₀ hTdiff hβmodel hVmodel
    (I.uniqueDiffOn y₀
      (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)))
  have hpair_deriv :
      fderivWithin 𝕜 (fun y : E => (Tm y (βm y)) (fun a : Fin s => Vm a y))
          (Set.range I) y₀ Xmodel =
        extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
          x₀ (X x₀) := by
    simpa [Tm, βm, Vm, Xmodel, y₀] using
      fderivWithin_tensorRS_eval_modelSlots_center_eq_extDerivFun
        (I := I) X T β V x₀ hpair
  have hcov_model : ∀ a : Fin s,
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
          (fun p : M => (cov (V a) p) (X p)) y₀ =
        fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a) := by
    intro a
    simpa [Vm, Xmodel, Γ, slots, y₀] using
      covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
        (I := I) cov X (V a) x₀ (hV a) (hVmodel a) (hcoord a)
  have hslots_center :
      (fun a : Fin s =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 x₀
          (slots a)) =
        fun a : Fin s => V a x₀ := by
    funext a
    simpa [slots, Vm] using tangentFieldModelInChart_center_symmL (I := I) (V a) x₀
  have hleft_model :
      (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x₀) (β x₀) (fun a : Fin s => V a x₀) =
        (covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E) r s
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I))
          (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
          Tm (Set.range I) y₀ (βm y₀)) slots := by
    have hβcenter :
        (trivializationAt (Tensor0SModel r 𝕜 E)
          (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x₀ (βm y₀) =
          β x₀ := by
      unfold βm tensor0SModelInChart tensor0SModelAt
      rw [extChartAt_to_inv]
      let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
        (fun x => Tensor0SSpace r I x) x₀
      change eβ.symmL 𝕜 x₀ ((eβ ⟨x₀, β x₀⟩).2) = β x₀
      have hcoord : (eβ ⟨x₀, β x₀⟩).2 = eβ.continuousLinearMapAt 𝕜 x₀ (β x₀) := by
        rw [Bundle.Trivialization.continuousLinearMapAt_apply]
        rw [eβ.coe_linearMapAt_of_mem (R := 𝕜)
          (FiberBundle.mem_baseSet_trivializationAt' x₀)]
      rw [hcoord]
      exact eβ.symmL_continuousLinearMapAt (R := 𝕜)
        (FiberBundle.mem_baseSet_trivializationAt' x₀) (β x₀)
    let F : (p : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H)
        (I := I) (M := M) r s p := fun p =>
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T p
    have hmodel :
        tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            r s x₀ F y₀ =
          covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E) r s
            (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
              (fun x => X x) (Set.range I))
            (connectionEndomorphismInChart
              (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
            Tm (Set.range I) y₀ := by
      unfold tensorRSModelInChart
      dsimp only [y₀]
      rw [extChartAt_to_inv]
      dsimp only [F]
      unfold nablaRSFun TensorLieDeriv.mcovariantDeriv_tensorRSFromConnection
        TensorLieDeriv.mcovariantDeriv_tensorRSWithinFromConnection
      rw [TensorLieDeriv.modelAt_mcovRS]
      simp only [Tm, Set.preimage_univ, Set.univ_inter]
    calc
      (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x₀) (β x₀) (fun a : Fin s => V a x₀) =
          (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
            (I := I) (M := M) r s x₀ F y₀ (βm y₀)) slots := by
            rw [tensorRSModelInChart_apply_modelSlots_center,
              hβcenter, hslots_center]
      _ = (covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E) r s
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I))
          (connectionEndomorphismInChart
            (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
          Tm (Set.range I) y₀ (βm y₀)) slots := by rw [hmodel]
  have hinput :
      (Tm y₀
        (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I))
          (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
          βm (Set.range I) y₀)) slots =
        (T x₀ (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀) := by
    have h := tensorRSModelInChart_apply_modelSlots_center
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (r := r) (s := s) (A := fun x => T x)
      (βm := covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I))
        (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
        βm (Set.range I) y₀)
      (slots := slots) x₀
    rw [hslots_center] at h
    simpa [Tm, βm, localCovariantDerivTensor0SAt, Xmodel, Γ, y₀] using h
  have houtput_sum :
      (∑ a : Fin s,
        (Tm y₀ (βm y₀))
          (Function.update (fun b : Fin s => Vm b y₀) a
            (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (Vm a y₀)))) =
        ∑ a : Fin s,
          (T x₀ (β x₀))
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcov_model a]
    simpa [Tm, βm, Vm, slots, y₀] using
      tensorRSModelInChart_apply_update_modelOutputSlot_center
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        (r := r) (s := s) (A := fun x => T x) (β := β)
        (V := V) (W := fun p : M => (cov (V a) p) (X p)) x₀ a
  calc
    (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s cov X T x₀) (β x₀) (fun a : Fin s => V a x₀)
        =
      (covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E) r s
          (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
            (fun x => X x) (Set.range I))
          (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
          Tm (Set.range I) y₀ (βm y₀)) slots := hleft_model
    _ =
      fderivWithin 𝕜 (fun y : E => (Tm y (βm y)) (fun a : Fin s => Vm a y))
          (Set.range I) y₀ Xmodel -
        (Tm y₀
          (covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) r
            (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
              (fun x => X x) (Set.range I))
            (connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀)
            βm (Set.range I) y₀))
          (fun a : Fin s => Vm a y₀) -
        ∑ a : Fin s,
          (Tm y₀ (βm y₀))
            (Function.update
              (fun b : Fin s => Vm b y₀)
              a
              (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (Vm a y₀))) := by
          simpa [Xmodel, Γ, slots] using hprod
    _ =
      extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
          x₀ (X x₀) -
        (T x₀ (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀) -
        ∑ a : Fin s,
          (T x₀ (β x₀))
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
          rw [hpair_deriv, hinput, houtput_sum]

theorem nablaRSFun_sub_raw {r s : ℕ}
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s)
    (β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r x)
    (V : Fin s -> (x : M) -> TangentSpace I x) (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => (T p (β p)) (fun a : Fin s => V a p)) x₀)
    (hβmodel : DifferentiableWithinAt 𝕜
      (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
        (M := M) r x₀ β)
      (Set.range I) (extChartAt I x₀ x₀))
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov X T x₀ (β x₀) (fun a : Fin s => V a x₀) -
      nablaRSFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        r s cov' X T x₀ (β x₀) (fun a : Fin s => V a x₀)) =
      -(((T x₀
          (localCovariantDerivTensor0SAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀))
          (fun a : Fin s => V a x₀)) -
        ((T x₀
          (localCovariantDerivTensor0SAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov' X β x₀))
          (fun a : Fin s => V a x₀))) -
      ∑ a : Fin s,
        (T x₀ (β x₀))
          (Function.update (fun b : Fin s => V b x₀) a
            (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀))) := by
  classical
  let slots : Fin s -> TangentSpace I x₀ := fun a => V a x₀
  have hcov := nablaRSFun_eval_moving_raw
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    cov X T β V x₀ hpair hβmodel hV hVmodel hcoord
  have hcov' := nablaRSFun_eval_moving_raw
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    cov' X T β V x₀ hpair hβmodel hV hVmodel hcoord
  have hdiff (a : Fin s) :
      (T x₀ (β x₀))
          (Function.update slots a ((cov (V a) x₀) (X x₀))) -
        (T x₀ (β x₀))
          (Function.update slots a ((cov' (V a) x₀) (X x₀))) =
        (T x₀ (β x₀))
          (Function.update slots a
            (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀))) := by
    have hconn :
        ((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀) =
          ((cov (V a) x₀) (X x₀)) - ((cov' (V a) x₀) (X x₀)) := by
      have h :=
        IsCovariantDerivativeOn.difference_apply
          (hcov := cov.isCovariantDerivativeOnUniv)
          (hcov' := cov'.isCovariantDerivativeOnUniv)
          (σ := V a) (x := x₀) (hx := by trivial) (hV a)
      exact congrArg (fun L : TangentSpace I x₀ →L[𝕜] TangentSpace I x₀ => L (X x₀)) h
    rw [hconn]
    exact ((T x₀ (β x₀)).map_update_sub slots a
      ((cov (V a) x₀) (X x₀))
      ((cov' (V a) x₀) (X x₀))).symm
  let D : 𝕜 :=
    extDerivFun (I := I) (fun p : M => (T p (β p)) (fun a : Fin s => V a p))
      x₀ (X x₀)
  let Lcov : 𝕜 :=
    (T x₀
      (localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X β x₀)) slots
  let Lcov' : 𝕜 :=
    (T x₀
      (localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov' X β x₀)) slots
  let Scov : 𝕜 :=
    ∑ a : Fin s, (T x₀ (β x₀))
      (Function.update slots a ((cov (V a) x₀) (X x₀)))
  let Scov' : 𝕜 :=
    ∑ a : Fin s, (T x₀ (β x₀))
      (Function.update slots a ((cov' (V a) x₀) (X x₀)))
  let Sdiff : 𝕜 :=
    ∑ a : Fin s,
      (T x₀ (β x₀))
        (Function.update slots a
          (((CovariantDerivative.difference cov cov' x₀) (V a x₀)) (X x₀)))
  have hsum : Scov - Scov' = Sdiff := by
    dsimp [Scov, Scov', Sdiff]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact hdiff a
  rw [hcov, hcov']
  change (D - Lcov - Scov) - (D - Lcov' - Scov') = -(Lcov - Lcov') - Sdiff
  rw [← hsum]
  abel

set_option backward.isDefEq.respectTransparency false in







theorem nabla0SFun_eval_coordFrame_moving_raw {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin s -> (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M)
    (hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => α p (fun a : Fin s => V a p)) x₀)
    (hV : ∀ a : Fin s, MDiffAt (T% (V a)) x₀)
    (hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α x₀) (fun a : Fin s => V a x₀) =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀) -
        ∑ a : Fin s,
          α x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
  classical
  let y₀ : E := extChartAt I x₀ x₀
  let Xmodel : E :=
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun x => X x) (Set.range I) y₀
  let αm : E -> Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
    tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s x₀ (fun x => α x)
  let Vm : Fin s -> E -> E :=
    fun a => tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
  let Γ : E →L[𝕜] E :=
    connectionEndomorphismInChart (𝕜 := 𝕜) (I := I) cov (fun x => X x) x₀ y₀
  let slots : Fin s -> E := fun a => Vm a y₀
  have hαdiff : DifferentiableWithinAt 𝕜 αm (Set.range I) y₀ := by
    have hcd := tensor0SModelInChart_contMDiffWithinAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s x₀ α
    have hdiff := hcd.contDiffWithinAt.differentiableWithinAt (by simp)
    simpa [αm, y₀] using hdiff
  have hprod :=
    fderivWithin_tensor0SModel_eval_slots
      (𝕜 := 𝕜) (E := E) (s := s) αm Vm (Set.range I) y₀ Xmodel
      hαdiff hVmodel
      (I.uniqueDiffOn y₀
        (extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)))
  have hpair_deriv :
      fderivWithin 𝕜 (fun y : E => αm y (fun a : Fin s => Vm a y))
          (Set.range I) y₀ Xmodel =
        extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
          x₀ (X x₀) := by
    simpa [αm, Vm, Xmodel, y₀] using
      fderivWithin_tensor0S_eval_modelSlots_center_eq_extDerivFun
        (I := I) X α V x₀ hpair
  have hcov_model : ∀ a : Fin s,
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀
          (fun p : M => (cov (V a) p) (X p)) y₀ =
        fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a) := by
    intro a
    simpa [Vm, Xmodel, Γ, slots, y₀] using
      covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
        (I := I) cov X (V a) x₀ (hV a) (hVmodel a) (hcoord a)
  have hfixed := fixedChartNabla0SModel_apply_slots
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) s cov X α x₀ y₀ slots
  have hself := nabla0SFun_apply_selfChart_slots
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    s cov X α x₀ slots
  have hslot :
      (fun a : Fin s =>
        tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (slots a) x₀) =
        fun a : Fin s => V a x₀ := by
    funext a
    simpa [slots, Vm, tangentConstInChart] using
      tangentFieldModelInChart_center_symmL (I := I) (V a) x₀
  have hcorr_sum :
      ∑ a : Fin s,
        αm y₀
          (Function.update slots a
            (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a))) =
      ∑ a : Fin s,
        α x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (V a) x₀) (X x₀))) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcov_model a]
    exact tensor0SModelInChart_apply_update_modelSlot_center
      (I := I) (fun x => α x) V (fun p : M => (cov (V a) p) (X p)) x₀ a
  calc
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α x₀) (fun a : Fin s => V a x₀)
        =
      (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α x₀)
        (fun a : Fin s =>
          tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (slots a) x₀) := by
          rw [hslot]
    _ = fixedChartNabla0SModel (𝕜 := 𝕜) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s cov X α x₀ y₀ slots := hself
    _ =
      fderivWithin 𝕜 αm (Set.range I) y₀ Xmodel slots -
        ∑ a : Fin s, αm y₀ (Function.update slots a (Γ (slots a))) := by
          simpa [αm, Xmodel, Γ, y₀] using hfixed
    _ =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
          x₀ (X x₀) -
        ∑ a : Fin s,
          αm y₀
            (Function.update slots a
              (fderivWithin 𝕜 (Vm a) (Set.range I) y₀ Xmodel + Γ (slots a))) := by
          rw [← hpair_deriv]
          rw [hprod]
          simp_rw [(αm y₀).map_update_add]
          rw [Finset.sum_add_distrib]
          abel
    _ =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
          x₀ (X x₀) -
        ∑ a : Fin s,
          α x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
          rw [hcorr_sum]
end Tensor0SBundle
