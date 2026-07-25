import DifferentialGeometry.Geometry.Coordinates.NablaComponents.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.ModelMixed
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase










set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]

private theorem fderivWithin_eq_sum_basis_coord
    {F : E -> E} {u : Set E} {y Xy : E}
    (hF : DifferentiableWithinAt 𝕜 F u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    fderivWithin 𝕜 F u y Xy =
      ∑ i : CoordinateIdx (𝕜 := 𝕜) E,
        fderivWithin 𝕜
          (fun z : E => (Module.finBasis 𝕜 E).coord i (F z)) u y Xy •
          (Module.finBasis 𝕜 E) i := by
  classical
  let b : Module.Basis (CoordinateIdx (𝕜 := 𝕜) E) 𝕜 E := Module.finBasis 𝕜 E
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
      (∑ j : CoordinateIdx (𝕜 := 𝕜) E,
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

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
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

omit [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
private theorem tangentFieldModelInChart_fderivWithin_eq_sum_extDerivFun_coord
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hVmodel :
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ i : CoordinateIdx (𝕜 := 𝕜) E,
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
      ∑ i : CoordinateIdx (𝕜 := 𝕜) E,
        extDerivFun (I := I)
          (fun p : M =>
            (Module.finBasis 𝕜 E).coord i
              (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
                (extChartAt I x₀ p))) x₀ (X x₀) •
          (Module.finBasis 𝕜 E) i := by
  classical
  let F : E -> E := tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
  let b : Module.Basis (CoordinateIdx (𝕜 := 𝕜) E) 𝕜 E := Module.finBasis 𝕜 E
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

omit [IsManifold I ∞ M] in
theorem covariantDerivative_modelInChart_center_eq_fderiv_plus_connection
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : MDiffAt (T% V) x₀)
    (hVmodel :
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀))
    (hcoord : ∀ i : CoordinateIdx (𝕜 := 𝕜) E,
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
  let zfun : CoordinateIdx (𝕜 := 𝕜) E -> M -> 𝕜 :=
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
      (∑ i : CoordinateIdx (𝕜 := 𝕜) E,
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

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 2 M] in
omit [IsManifold I ∞ M] in
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

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] [IsManifold I ∞ M] in
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

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] [IsManifold I ∞ M] in
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

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] [IsManifold I ∞ M] in
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

set_option backward.isDefEq.respectTransparency false in







omit [IsManifold I ∞ M] in
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
    (hcoord : ∀ a : Fin s, ∀ i : CoordinateIdx (𝕜 := 𝕜) E,
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

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 2 M] in
private theorem tangentFieldModelInChart_contDiffWithinAt_center_of_contMDiffAt
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M => (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    ContDiffWithinAt 𝕜 (∞ : WithTop ℕ∞)
      (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
      (Set.range I) (extChartAt I x₀ x₀) := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hx : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hcoord :
      ContMDiffAt I 𝓘(𝕜, E) (∞ : WithTop ℕ∞)
        (fun p : M => (e ⟨p, V p⟩).2) x₀ :=
    (e.contMDiffAt_section_iff hx).mp hV
  have hsymm :
      ContMDiffWithinAt 𝓘(𝕜, E) I (∞ : WithTop ℕ∞)
        (extChartAt I x₀).symm (Set.range I) (extChartAt I x₀ x₀) := by
    simpa using
      contMDiffWithinAt_extChartAt_symm_range_self
        (I := I) (n := (∞ : WithTop ℕ∞)) x₀
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  have hcoord_center :
      ContMDiffAt I 𝓘(𝕜, E) (∞ : WithTop ℕ∞)
        (fun p : M => (e ⟨p, V p⟩).2)
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    simpa [hcenter] using hcoord
  have hfixed :
      ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E) (∞ : WithTop ℕ∞)
        ((fun p : M => (e ⟨p, V p⟩).2) ∘ (extChartAt I x₀).symm)
        (Set.range I) (extChartAt I x₀ x₀) :=
    hcoord_center.comp_contMDiffWithinAt (x := extChartAt I x₀ x₀) hsymm
  have heq :
      tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
        =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
      (fun p : M => (e ⟨p, V p⟩).2) ∘ (extChartAt I x₀).symm := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
    have hp_source : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    have hp_base : (extChartAt I x₀).symm y ∈ e.baseSet := by
      simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
    have hcoe :
        ⇑(e.linearMapAt 𝕜 ((extChartAt I x₀).symm y)) =
          fun z => (e ⟨(extChartAt I x₀).symm y, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := 𝕜) hp_base
    unfold tangentFieldModelInChart
    change e.linearMapAt 𝕜 ((extChartAt I x₀).symm y)
        (V ((extChartAt I x₀).symm y)) =
      (e ⟨(extChartAt I x₀).symm y, V ((extChartAt I x₀).symm y)⟩).2
    rw [hcoe]
  have hmdiff :
      ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E) (∞ : WithTop ℕ∞)
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
        (Set.range I) (extChartAt I x₀ x₀) := by
    refine hfixed.congr_of_eventuallyEq heq ?_
    have hy : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target :=
      mem_extChartAt_target (I := I) x₀
    have hp_source :
        (extChartAt I x₀).symm (extChartAt I x₀ x₀) ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy
    have hp_base : (extChartAt I x₀).symm (extChartAt I x₀ x₀) ∈ e.baseSet := by
      simp [e, TangentBundle.trivializationAt_baseSet] at hp_source ⊢
    have hcoe :
        ⇑(e.linearMapAt 𝕜 ((extChartAt I x₀).symm (extChartAt I x₀ x₀))) =
          fun z => (e ⟨(extChartAt I x₀).symm (extChartAt I x₀ x₀), z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := 𝕜) hp_base
    unfold tangentFieldModelInChart
    change e.linearMapAt 𝕜 ((extChartAt I x₀).symm (extChartAt I x₀ x₀))
        (V ((extChartAt I x₀).symm (extChartAt I x₀ x₀))) =
      (e ⟨(extChartAt I x₀).symm (extChartAt I x₀ x₀),
        V ((extChartAt I x₀).symm (extChartAt I x₀ x₀))⟩).2
    rw [hcoe]
  exact hmdiff.contDiffWithinAt

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 2 M] in
private theorem tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M => (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    DifferentiableWithinAt 𝕜
      (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
      (Set.range I) (extChartAt I x₀ x₀) := by
  exact (tangentFieldModelInChart_contDiffWithinAt_center_of_contMDiffAt
    (I := I) V x₀ hV).differentiableWithinAt (by simp)

omit [IsManifold I 2 M] in
private theorem tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M => (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀)
    (i : CoordinateIdx (𝕜 := 𝕜) E) :
    MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M =>
        (Module.finBasis 𝕜 E).coord i
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ p))) x₀ := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hx : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hcoord :
      ContMDiffAt I 𝓘(𝕜, E) (∞ : WithTop ℕ∞)
        (fun p : M => (e ⟨p, V p⟩).2) x₀ :=
    (e.contMDiffAt_section_iff hx).mp hV
  have hscalar :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => (Module.finBasis 𝕜 E).coord i ((e ⟨p, V p⟩).2)) x₀ :=
    (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord i)).contMDiffAt.comp
      x₀ hcoord
  have heq :
      (fun p : M =>
        (Module.finBasis 𝕜 E).coord i
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ p)))
        =ᶠ[𝓝 x₀]
      fun p : M => (Module.finBasis 𝕜 E).coord i ((e ⟨p, V p⟩).2) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with p hp
    have hp_source : p ∈ (extChartAt I x₀).source := by
      simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp
    have hleft : (extChartAt I x₀).symm (extChartAt I x₀ p) = p :=
      (extChartAt I x₀).left_inv hp_source
    have hcoe :
        ⇑(e.linearMapAt 𝕜 p) = fun z => (e ⟨p, z⟩).2 :=
      e.coe_linearMapAt_of_mem (R := 𝕜) hp
    unfold tangentFieldModelInChart
    rw [hleft]
    change (Module.finBasis 𝕜 E).coord i
        (e.linearMapAt 𝕜 p (V p)) =
      (Module.finBasis 𝕜 E).coord i ((e ⟨p, V p⟩).2)
    rw [hcoe]
  exact (hscalar.congr_of_eventuallyEq heq).mdifferentiableAt (by simp)

set_option backward.isDefEq.respectTransparency false in





omit [IsManifold I 2 M] in
theorem tensor0S_eval_coordinateFrame_contMDiffAt
    {s : ℕ}
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun y : M => α y (fun a : Fin s => coordinateFrameAt (I := I) x₀ (slots a) y))
      x₀ := by
  have hα_top := α.contMDiff x₀
  have hα := hα_top.of_le
    (by simp : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hframe :
      ∀ a : Fin s,
        ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
          (fun y : M =>
            (⟨y, coordinateFrameAt (I := I) x₀ (slots a) y⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    intro a
    exact (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) (slots a)
  have hEval := TensorMultilinear.contMDiffAt_section_apply_gen
    (I := I) (M := M) (n := s) (x₀ := x₀)
    (T := fun y : M => α y) hα
    (v := fun a : Fin s => coordinateFrameAt (I := I) x₀ (slots a))
    (hv := hframe)
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using hEval

omit [IsManifold I 2 M] in
omit [CompleteSpace 𝕜] in
private theorem coordinateFrame_covariantDeriv_apply_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, (cov (coordinateFrameAt (I := I) x₀ j) p) (X p)⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
  let u := coordinateFrameSet (I := I) x₀
  let frame := coordinateFrameAt (I := I) x₀
  have hu : IsOpen u := coordinateFrameSet_open (I := I) x₀
  have hx₀ : x₀ ∈ u := coordinateFrameAt_mem (I := I) x₀
  have hframe_smooth :
      CMDiff[u] ((∞ : WithTop ℕ∞) + 1) (T% (frame j)) := by
    exact ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffOn j).of_le
      (by simp)
  have hcov_frame :
      ContMDiffOn I (I.prod 𝓘(𝕜, E →L[𝕜] E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, cov (frame j) p⟩ :
            TotalSpace (E →L[𝕜] E)
              (fun p : M => TangentSpace I p →L[𝕜] TangentSpace I p)))
        u := by
    simpa [u, frame] using (hcov hu).contMDiff hframe_smooth
  have hX_on :
      CMDiff[u] (∞ : WithTop ℕ∞) (T% (fun p : M => X p)) :=
    (X.contMDiff.of_le (by simp :
      (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))).contMDiffOn
  have hW_on :
      ContMDiffOn I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, (cov (frame j) p) (X p)⟩ :
            TotalSpace E (TangentSpace I : M -> Type _)))
        u := by
    simpa [frame] using hcov_frame.clm_bundle_apply hX_on
  exact (hW_on x₀ hx₀).contMDiffAt (hu.mem_nhds hx₀)

set_option backward.isDefEq.respectTransparency false in


omit [IsManifold I 2 M] in
theorem tensor0S_eval_coordinateFrame_covariantDerivative_slot_contMDiffAt
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) (a : Fin s) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        α p
          (Function.update
            (fun b : Fin s => coordinateFrameAt (I := I) x₀ (slots b) p)
            a
            ((cov (coordinateFrameAt (I := I) x₀ (slots a)) p) (X p))))
      x₀ := by
  let αinf : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
    ⟨fun p : M => α p, α.contMDiff.of_le (by simp)⟩
  let W : (p : M) -> TangentSpace I p :=
    fun p : M => (cov (coordinateFrameAt (I := I) x₀ (slots a)) p) (X p)
  have hW :
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M => (⟨p, W p⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        x₀ := by
    simpa [W] using
      coordinateFrame_covariantDeriv_apply_contMDiffAt
        (I := I) cov hcov X x₀ (slots a)
  have hframe :
      ∀ i : Fin s,
        ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p,
              Function.update
                (fun b : Fin s => coordinateFrameAt (I := I) x₀ (slots b) p)
                a
                (W p) i⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    intro i
    by_cases hi : i = a
    · subst hi
      simpa using hW
    · have hbase :
          ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
            (fun p : M =>
              (⟨p, coordinateFrameAt (I := I) x₀ (slots i) p⟩ :
                TotalSpace E (TangentSpace I : M -> Type _))) x₀ :=
        (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
          (coordinateFrameSet_open (I := I) x₀)
          (coordinateFrameAt_mem (I := I) x₀) (slots i)
      simpa [Function.update, hi] using hbase
  have hEval := TensorMultilinear.contMDiffAt_section_apply_gen
    (I := I) (M := M) (n := s) (x₀ := x₀)
    (T := fun p : M => αinf p) αinf.contMDiff.contMDiffAt
    (v := fun i : Fin s =>
      fun p : M =>
        Function.update
          (fun b : Fin s => coordinateFrameAt (I := I) x₀ (slots b) p)
          a
          (W p) i)
    (hv := hframe)
  simpa [αinf, W, Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    using hEval

set_option backward.isDefEq.respectTransparency false in




theorem nabla0SFun_eval_coordinateFrame_contMDiffAt
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α p)
          (fun a : Fin s => coordinateFrameAt (I := I) x₀ (slots a) p)) x₀ := by
  let V : Fin s -> (p : M) -> TangentSpace I p :=
    fun a => coordinateFrameAt (I := I) x₀ (slots a)
  let pair : M -> 𝕜 := fun p : M => α p (fun a : Fin s => V a p)
  let Xinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => X p, X.contMDiff.of_le (by simp)⟩
  have hpair : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair x₀ := by
    simpa [pair, V] using tensor0S_eval_coordinateFrame_contMDiffAt
      (I := I) α x₀ slots
  have hderiv :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => extDerivFun (I := I) pair p (X p)) x₀ :=
    extDerivFun_apply_contMDiffAt (I := I) hpair Xinf
  have hcorr_sum :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          ∑ a : Fin s,
            α p
              (Function.update
                (fun b : Fin s => coordinateFrameAt (I := I) x₀ (slots b) p)
                a
                ((cov (coordinateFrameAt (I := I) x₀ (slots a)) p) (X p)))) x₀ := by
    apply ContMDiffAt.sum
    intro a _
    exact tensor0S_eval_coordinateFrame_covariantDerivative_slot_contMDiffAt
      (I := I) cov hcov X α x₀ slots a
  have hmain :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          extDerivFun (I := I) pair p (X p) -
            ∑ a : Fin s,
              α p
                (Function.update
                  (fun b : Fin s => coordinateFrameAt (I := I) x₀ (slots b) p)
                  a
                  ((cov (coordinateFrameAt (I := I) x₀ (slots a)) p) (X p)))) x₀ :=
    hderiv.sub hcorr_sum
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with p hp
  have hV_at : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun y : M => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) p := by
    intro a
    simpa [V] using
      (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
        (coordinateFrameSet_open (I := I) x₀) hp (slots a)
  have hpair_md : MDifferentiableAt I 𝓘(𝕜, 𝕜) pair p := by
    have hpair_p : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair p := by
      have hα_top := α.contMDiff p
      have hα := hα_top.of_le
        (by simp : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
      have hEval := TensorMultilinear.contMDiffAt_section_apply_gen
        (I := I) (M := M) (n := s) (x₀ := p)
        (T := fun y : M => α y) hα
        (v := fun a : Fin s => V a)
        (hv := hV_at)
      simpa [pair, Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
        using hEval
    exact hpair_p.mdifferentiableAt (by simp)
  have hV_md : ∀ a : Fin s, MDiffAt (T% (V a)) p :=
    fun a => (hV_at a).mdifferentiableAt (by simp)
  have hVmodel_p : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) p (V a))
        (Set.range I) (extChartAt I p p) :=
    fun a =>
      tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
        (I := I) (V a) p (hV_at a)
  have hcoord_p : ∀ a : Fin s, ∀ i : CoordinateIdx (𝕜 := 𝕜) E,
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun q : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) p (V a)
              (extChartAt I p q))) p :=
    fun a i =>
      tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
        (I := I) (V a) p (hV_at a) i
  rw [nabla0SFun_eval_coordFrame_moving_raw
    (I := I) cov X V α p hpair_md hV_md hVmodel_p hcoord_p]

set_option backward.isDefEq.respectTransparency false in






theorem nabla0SFun_contMDiff_of_eval_coordinateFrame_contMDiffAt
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (hcoeff : ∀ x₀ : M, ∀ slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E,
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            s cov X α p)
            (fun a : Fin s => coordinateFrameAt (I := I) x₀ (slots a) p))
        x₀) :
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s
    ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel s 𝕜 E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α p⟩ :
          TotalSpace (Tensor0SModel s 𝕜 E) (fun p : M => Tensor0SSpace s I p))) := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) s
  let F : (p : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s p :=
    fun p : M =>
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α p
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
    (∞ : WithTop ℕ∞) b F).mpr ?_
  intro σ x₀
  have hframe_eval := hcoeff x₀ σ
  refine hframe_eval.congr_of_eventuallyEq ?_
  filter_upwards
    [(coordinateFrameSet_open (I := I) x₀).mem_nhds
      (coordinateFrameAt_mem (I := I) x₀)] with p hp
  have hslot :
      (fun a : Fin s =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 p
            (b (σ a))) =
        fun a : Fin s => coordinateFrameAt (I := I) x₀ (σ a) p := by
    funext a
    have hp_src : p ∈ (chartAt H x₀).source := by
      simpa [coordinateFrameSet, coordinateTrivializationAt] using hp
    rw [coordinateFrameAt_apply_of_mem (I := I) (x₀ := x₀) (x := p) hp (σ a)]
    simpa [b] using
      congrArg
        (fun L : E →L[𝕜] TangentSpace I p => L (b (σ a)))
        (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hp_src)
  rw [continuousMultilinearMap_basis_repr]
  change ((trivializationAt (Tensor0SModel s 𝕜 E)
      (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M -> Type _)) x₀
      ⟨p, F p⟩).2)
      (fun a : Fin s => b (σ a)) =
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α p) (fun a : Fin s => coordinateFrameAt (I := I) x₀ (σ a) p)
  change (F p).compContinuousLinearMap
      (fun _ : Fin s =>
        (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 p)
      (fun a : Fin s => b (σ a)) =
    F p (fun a : Fin s => coordinateFrameAt (I := I) x₀ (σ a) p)
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hslot]

set_option backward.isDefEq.respectTransparency false in







theorem nabla0SFun_contMDiff
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s
    ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel s 𝕜 E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α p⟩ :
          TotalSpace (Tensor0SModel s 𝕜 E) (fun p : M => Tensor0SSpace s I p))) := by
  exact Tensor0SBundle.nabla0S_reg
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov hcov X α

set_option backward.isDefEq.respectTransparency false in







noncomputable def nabla0SCoord (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) s
  ⟨fun p : M =>
    nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α p,
    nabla0SFun_contMDiff (I := I) cov hcov X α⟩

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem nabla0SCoord_apply (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (p : M) :
    nabla0SCoord (I := I) s cov hcov X α p =
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α p := by
  rfl

end DifferentialGeometry.Tensor.Coordinates
