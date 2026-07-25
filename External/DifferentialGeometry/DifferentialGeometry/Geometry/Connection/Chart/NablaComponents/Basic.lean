import DifferentialGeometry.Geometry.Connection.Chart.Christoffel
import DifferentialGeometry.Geometry.Connection.Chart.CoordinateFrame
import DifferentialGeometry.Tensor.RSTensor.Derivation.NablaOnTensors

set_option linter.flexible false
set_option linter.unnecessarySimpa false



noncomputable section

namespace DifferentialGeometry
namespace Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

def coordinateFrameAt_isLocalFrame_one (x₀ : M) :
    IsLocalFrameOn I E (1 : WithTop ℕ∞)
      (coordinateFrameAt (I := I) x₀) (coordinateFrameSet (I := I) x₀) :=
  (coordinateTrivializationAt (I := I) x₀).isLocalFrameOn_localFrame_baseSet
    I (1 : WithTop ℕ∞) (Module.finBasis Real E)

theorem coordinateFrameAt_toBasis_eq_finBasis (x₀ : M) :
    coordinateFrameAt_toBasis (I := I) x₀ = Module.finBasis Real E := by
  ext i
  rw [coordinateFrameAt_toBasis_apply]
  rw [coordinateFrameAt_apply_of_mem (I := I) (coordinateFrameAt_mem (I := I) x₀) i]
  rw [mfderivWithin_range_extChartAt_symm]
  rfl

private theorem tangentConstInChart_eq_coordinateFrame_eventually
    (x₀ : M) (i : CoordinateIdx E) :
    (tangentConstInChart (𝕜 := Real) (I := I) x₀ ((Module.finBasis Real E) i) :
        (x : M) → TangentSpace I x) =ᶠ[𝓝 x₀]
      coordinateFrameAt (I := I) x₀ i := by
  filter_upwards
    [((coordinateTrivializationAt (I := I) x₀).open_baseSet.mem_nhds
      (coordinateFrameAt_mem (I := I) x₀))] with x hx
  have hx_src : x ∈ (chartAt H x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  rw [tangentConstInChart_apply]
  rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hx_src]
  rw [coordinateFrameAt_apply_of_mem (I := I) (x₀ := x₀) (x := x) hx i]
  rfl

theorem connCoeff_eq_christoffelAlong_coord
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : (x : M) -> TangentSpace I x) (x₀ : M)
    (j k : CoordinateIdx E) :
    connectionEndomorphismCoeff (𝕜 := Real) (E := E) (Module.finBasis Real E)
        (connectionEndomorphismInChart (𝕜 := Real) (I := I) cov X x₀
          (extChartAt I x₀ x₀)) j k =
      christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
        x₀ (X x₀) j k := by
  classical
  let e := coordinateTrivializationAt (I := I) x₀
  have hx_base : x₀ ∈ e.baseSet := by
    simp [e, coordinateTrivializationAt]
  have hconst :
      MDiffAt
        (T% (tangentConstInChart (𝕜 := Real) (I := I) x₀
          ((Module.finBasis Real E) j) : (x : M) → TangentSpace I x)) x₀ :=
    mdifferentiableAt_tangentConstInChart_of_mem
      (𝕜 := Real) (I := I) (x₀ := x₀) (p := x₀)
      ((Module.finBasis Real E) j) hx_base
  have hframe :
      MDiffAt (T% (coordinateFrameAt (I := I) x₀ j)) x₀ :=
    ((coordinateFrameAt_isLocalFrame_one (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀)
      (coordinateFrameAt_mem (I := I) x₀) j).mdifferentiableAt one_ne_zero
  have hcov :
      cov (tangentConstInChart (𝕜 := Real) (I := I) x₀
            ((Module.finBasis Real E) j)) x₀ =
        cov (coordinateFrameAt (I := I) x₀ j) x₀ :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hconst hframe
      (by simp)
      (tangentConstInChart_eq_coordinateFrame_eventually (I := I) x₀ j)
  unfold connectionEndomorphismCoeff christoffelAlongInFrame
  rw [connectionEndomorphismInChart_apply_of_mem
    (𝕜 := Real) (I := I) cov X x₀ (mem_extChartAt_target x₀)
    ((Module.finBasis Real E) j)]
  rw [extChartAt_to_inv]
  rw [hcov]
  have hcoeff :
      ((coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff k x₀
        ((cov (coordinateFrameAt (I := I) x₀ j) x₀) (X x₀))) =
        (Module.finBasis Real E).coord k
          ((coordinateTrivializationAt (I := I) x₀).continuousLinearMapAt Real x₀
            ((cov (coordinateFrameAt (I := I) x₀ j) x₀) (X x₀))) := by
    have hbasis (hx : x₀ ∈ coordinateFrameSet (I := I) x₀) :
        (coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt hx =
          (coordinateTrivializationAt (I := I) x₀).basisAt
            (Module.finBasis Real E)
            (by simpa [coordinateFrameSet, coordinateTrivializationAt] using hx) := by
      ext a
      rw [IsLocalFrameOn.toBasisAt_coe]
      simp [coordinateFrameAt,
        coordinateTrivializationAt]
    unfold IsLocalFrameOn.coeff
    rw [dif_pos (coordinateFrameAt_mem (I := I) x₀)]
    rw [hbasis (coordinateFrameAt_mem (I := I) x₀)]
    simp [Bundle.Trivialization.basisAt]
    rw [Bundle.Trivialization.linearMapAt_apply]
    simp [coordinateTrivializationAt]
  rw [hcoeff]

def coordDeriv0SAt {s : ℕ}
    (X : (x : M) -> TangentSpace I x) (x₀ : M)
    (α : (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) s x)
    (slots : Fin s -> CoordinateIdx E) : Real :=
  mfderiv I 𝓘(Real, Real)
    (fun y : M => α y (fun a => coordinateFrameAt (I := I) x₀ (slots a) y))
    x₀ (X x₀)

def modelDeriv0SAt {s : ℕ}
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (α : (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) s x)
    (slots : Fin s -> CoordinateIdx E) : Real :=
  let X' := VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x₀).symm
    (fun x => X x) (Set.range I)
  let α' : E -> ContinuousMultilinearMap Real (fun _ : Fin s => E) Real :=
    fun y => tensor0SModelInChart (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s x₀ α y
  fderivWithin Real α'
    (((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I)
    (extChartAt I x₀ x₀) (X' (extChartAt I x₀ x₀))
    (fun a => (Module.finBasis Real E) (slots a))

def ModelDerivEqCoordDeriv0SAt {s : ℕ}
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (α : (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) s x) : Prop :=
  forall slots : Fin s -> CoordinateIdx E,
    modelDeriv0SAt (I := I) X x₀ α slots =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ α slots

theorem tensor0SModelAt_coordComponent0SAt {s : ℕ} (x₀ : M)
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x₀)
    (slots : Fin s -> CoordinateIdx E) :
    tensor0SModelAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s x₀ x₀ A (fun a => (Module.finBasis Real E) (slots a)) =
      coordComponent0SAt (I := I) A slots := by
  rw [coordComponent0SAt_apply]
  rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
  change
    (((trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousMultilinearMap
        Real s) ⟨x₀, A⟩).2 (fun a => (Module.finBasis Real E) (slots a)) =
      A (fun a => (Module.finBasis Real E) (slots a))
  rw [Bundle.Trivialization.continuousMultilinearMap_apply]
  change
    A (fun a =>
      (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real x₀
        ((Module.finBasis Real E) (slots a))) =
      A (fun a => (Module.finBasis Real E) (slots a))
  congr 1
  funext a
  have hx_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hx_src]
  rw [mfderivWithin_range_extChartAt_symm]
  rfl

private theorem model_component_eq_coord_component_comp_eventually {s : ℕ}
    (x₀ : M)
    (α : (x : M) -> Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) s x)
    (slots : Fin s -> CoordinateIdx E) :
    (fun y : E =>
        tensor0SModelInChart (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s x₀ α y (fun a => (Module.finBasis Real E) (slots a))) =ᶠ[
      𝓝[Set.range I] (extChartAt I x₀ x₀)]
    (fun y : E =>
        α ((extChartAt I x₀).symm y)
          (fun a => coordinateFrameAt (I := I) x₀ (slots a)
            ((extChartAt I x₀).symm y))) := by
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
  unfold tensor0SModelInChart tensor0SModelAt
  change
    (((trivializationAt E (TangentSpace I : M -> Type _) x₀).continuousMultilinearMap
        Real s) ⟨(extChartAt I x₀).symm y, α ((extChartAt I x₀).symm y)⟩).2
        (fun a => (Module.finBasis Real E) (slots a)) =
      α ((extChartAt I x₀).symm y)
        (fun a => coordinateFrameAt (I := I) x₀ (slots a) ((extChartAt I x₀).symm y))
  rw [Bundle.Trivialization.continuousMultilinearMap_apply]
  change
    α ((extChartAt I x₀).symm y)
        (fun a =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real
            ((extChartAt I x₀).symm y) ((Module.finBasis Real E) (slots a))) =
      α ((extChartAt I x₀).symm y)
        (fun a => coordinateFrameAt (I := I) x₀ (slots a) ((extChartAt I x₀).symm y))
  congr 1
  funext a
  have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I x₀).map_target hy
  have hy_base : (extChartAt I x₀).symm y ∈ coordinateFrameSet (I := I) x₀ := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hy_src
  rw [coordinateFrameAt_apply_of_mem (I := I) hy_base (slots a)]
  rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := Real) hy_src]
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem modelDeriv_eq_coordDeriv0SAt {s : ℕ}
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s) :
    ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) s
  letI := Tensor0SBundle.tensor0SBundle_fiber (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) s
  letI := Tensor0SBundle.tensor0SBundle_vector (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := M) s
  letI : NormedSpace Real
      (ContinuousMultilinearMap Real (fun _ : Fin s => E) Real) :=
    Tensor0SBundle.tensor0SModel_normedSpace (𝕜 := Real) (E := E) s
  letI : NormedSpace Real (Tensor0SModel s Real E) :=
    Tensor0SBundle.tensor0SModel_normedSpace (𝕜 := Real) (E := E) s
  intro slots
  let z₀ : E := extChartAt I x₀ x₀
  let S : Set E := ((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I
  let u : Fin s -> E := fun a => (Module.finBasis Real E) (slots a)
  let Achart : E -> ContinuousMultilinearMap Real (fun _ : Fin s => E) Real :=
    fun y => tensor0SModelInChart (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s x₀ (fun x => α x) y
  let f : M -> Real :=
    fun y => α y (fun a => coordinateFrameAt (I := I) x₀ (slots a) y)
  have hS : S = Set.range I := by
    ext y
    simp [S]
  have hzRange : z₀ ∈ Set.range I := by
    exact extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
  have hzS : z₀ ∈ S := by
    simpa [hS] using hzRange
  have huniq : UniqueDiffWithinAt Real S z₀ := by
    simpa [hS, z₀] using I.uniqueDiffOn z₀ hzRange
  have hX :
      VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) z₀ =
        X x₀ := by
    simp only [z₀, VectorField.mpullbackWithin_apply]
    rw [extChartAt_to_inv]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x₀) (X x₀)
  have hmodel_eventually :
      (fun y : E => Achart y u) =ᶠ[𝓝[S] z₀]
        writtenInExtChartAt I 𝓘(Real, Real) x₀ f := by
    have h := model_component_eq_coord_component_comp_eventually
      (I := I) (M := M) (s := s) x₀ (fun x => α x) slots
    simpa [S, z₀, Achart, u, f, writtenInExtChartAt] using h
  have hα_model := by
    have h := α.contMDiff x₀
    rw [contMDiffAt_section] at h
    simpa [tensor0SModelAt, Tensor0SModel] using h
  have hsymm :
      ContMDiffWithinAt 𝓘(Real, E) I (⊤ : WithTop ℕ∞)
        (extChartAt I x₀).symm S z₀ := by
    simpa [S, z₀] using
      contMDiffWithinAt_extChartAt_symm_range_self
        (I := I) (n := (⊤ : WithTop ℕ∞)) x₀
  have hα_model_center :
      ContMDiffAt I
        𝓘(Real, ContinuousMultilinearMap Real (fun _ : Fin s => E) Real)
        (⊤ : WithTop ℕ∞)
        (fun x : M =>
          tensor0SModelAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s x₀ x (α x))
        ((extChartAt I x₀).symm z₀) := by
    simpa [z₀, extChartAt_to_inv] using hα_model
  have hAchart_cd := by
    have hcomp := ContMDiffAt.comp_contMDiffWithinAt
      (I := 𝓘(Real, E)) (I' := I)
      (I'' := 𝓘(Real, ContinuousMultilinearMap Real (fun _ : Fin s => E) Real))
      (x := z₀) hα_model_center hsymm
    simpa [Achart, tensor0SModelInChart, Function.comp, z₀] using hcomp
  have hAchart_diff :
      DifferentiableWithinAt Real Achart S z₀ := by
    exact hAchart_cd.contDiffWithinAt.differentiableWithinAt (by simp)
  have hscalar_diff :
      DifferentiableWithinAt Real (fun y : E => Achart y u) S z₀ := by
    exact hAchart_diff.continuousMultilinear_apply_const u
  have hwritten_diff :
      DifferentiableWithinAt Real
        (writtenInExtChartAt I 𝓘(Real, Real) x₀ f) (Set.range I) z₀ := by
    have hscalar_diff_range :
        DifferentiableWithinAt Real (fun y : E => Achart y u) (Set.range I) z₀ := by
      simpa [hS] using hscalar_diff
    have hmodel_range :
        (fun y : E => Achart y u) =ᶠ[𝓝[Set.range I] z₀]
          writtenInExtChartAt I 𝓘(Real, Real) x₀ f := by
      simpa [hS] using hmodel_eventually
    exact (hmodel_range.differentiableWithinAt_iff_of_mem hzRange).mp hscalar_diff_range
  have hf_md : MDifferentiableAt I 𝓘(Real, Real) f x₀ := by
    rw [mdifferentiableAt_iff_source_of_mem_source (I := I) (I' := 𝓘(Real, Real))
      (x := x₀) (x' := x₀) (mem_chart_source H x₀)]
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
    simpa [writtenInExtChartAt, z₀, extChartAt, Function.comp_def] using hwritten_diff
  unfold modelDeriv0SAt coordDeriv0SAt
  change
    (fderivWithin Real Achart S z₀
        (VectorField.mpullbackWithin 𝓘(Real, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) z₀)) u =
      (mfderiv I 𝓘(Real, Real) f x₀) (X x₀)
  rw [hX, hf_md.mfderiv]
  have happly :
      (fderivWithin Real Achart S z₀ (X x₀)) u =
        fderivWithin Real (fun y : E => Achart y u) S z₀ (X x₀) := by
    exact (fderivWithin_continuousMultilinear_apply_const_apply
      huniq hAchart_diff u (X x₀)).symm
  rw [happly]
  have hfd :
      fderivWithin Real (fun y : E => Achart y u) S z₀ =
        fderivWithin Real (writtenInExtChartAt I 𝓘(Real, Real) x₀ f) S z₀ :=
    hmodel_eventually.fderivWithin_eq_of_mem hzS
  rw [hfd]
  rw [hS]
  rfl

theorem nabla0S_coordFrame_slots {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (x₀ : M) (hderiv : ModelDerivEqCoordDeriv0SAt (I := I) X x₀ (fun x => α x))
    (slots : Fin s -> CoordinateIdx E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x₀)
        slots =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x) slots -
        ∑ a : Fin s, ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) (slots a) k *
            coordComponent0SAt (I := I) (α x₀) (Function.update slots a k) := by
  classical
  simp only [nabla0SFun, TensorLieDeriv.mcovariantDeriv_tensor0SFromConnection,
    TensorLieDeriv.mcovariantDeriv_tensor0SWithinFromConnection]
  rw [← tensor0SModelAt_coordComponent0SAt (I := I) x₀
    (TensorLieDeriv.mcovariantDeriv_tensor0SWithin
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s X
      (connectionEndomorphismInChart (𝕜 := Real) (I := I) cov (fun x => X x) x₀)
      α Set.univ x₀) slots]
  have hmodel := TensorLieDeriv.mcovariantDeriv_tensor0SWithin_apply_basis_slots
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (⊤ : WithTop ℕ∞)) (Idx := CoordinateIdx E)
    (basis := Module.finBasis Real E)
    (X := X)
    (ΓX := connectionEndomorphismInChart (𝕜 := Real) (I := I) cov (fun x => X x) x₀)
    (α := α)
    (u := Set.univ)
    (x₀ := x₀)
    (slots := slots)
  refine hmodel.trans ?_
  simp_rw [connCoeff_eq_christoffelAlong_coord (I := I) cov (fun x => X x) x₀]
  change
    modelDeriv0SAt (I := I) X x₀ (fun x => α x) slots -
        (∑ a : Fin s, ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) (slots a) k *
            (tensor0SModelAt (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              s x₀ x₀ (α x₀))
              (Function.update (fun b : Fin s => (Module.finBasis Real E) (slots b))
                a ((Module.finBasis Real E) k))) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x) slots -
        ∑ a : Fin s, ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) (slots a) k *
            coordComponent0SAt (I := I) (α x₀) (Function.update slots a k)
  rw [hderiv slots]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [← tensor0SModelAt_coordComponent0SAt (I := I) x₀ (α x₀)
    (Function.update slots a k)]
  congr 1
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · simp [Function.update, hb]

theorem nabla0S_coordFrame_slots_of_smooth {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (⊤ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (⊤ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin s -> CoordinateIdx E) :
    coordComponent0SAt (I := I)
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X α x₀)
        slots =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x) slots -
        ∑ a : Fin s, ∑ k : CoordinateIdx E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀)
            x₀ (X x₀) (slots a) k *
            coordComponent0SAt (I := I) (α x₀) (Function.update slots a k) := by
  exact nabla0S_coordFrame_slots (I := I) cov X α x₀
    (modelDeriv_eq_coordDeriv0SAt (I := I) X x₀ α) slots

end Coordinates
end DifferentialGeometry
