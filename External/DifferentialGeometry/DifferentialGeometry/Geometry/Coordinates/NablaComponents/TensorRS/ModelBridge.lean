import DifferentialGeometry.Geometry.Coordinates.NablaComponents.TensorRS.Basic








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




omit [IsManifold I 2 M] in
theorem tensorRSModelAt_coordComponentRSAt {r s : ℕ} (x₀ : M)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    (tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      r s x₀ x₀ T
      ((continuousMultilinearMap_basis
        (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper))
      (fun b : Fin s => (Module.finBasis 𝕜 E) (lower b))
    =
      coordComponentRSAt (I := I) T upper lower := by
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) r s
  letI := tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) r s
  letI : NormedSpace 𝕜 (Tensor0SModel r 𝕜 E) :=
    Tensor0SBundle.tensor0SModel_normedSpace (𝕜 := 𝕜) (E := E) r
  unfold tensorRSModelAt
  rw [coordComponentRSAt_apply, componentRS_apply_gen]
  have hx : x₀ ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
    exact mem_baseSet_trivializationAt E (TangentSpace I : M -> Type _) x₀
  rw [TensorRSSpace.trivializationAt_basis_coord
    (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := x₀) (r := r) (s := s)
    (bE := Module.finBasis 𝕜 E) hx T upper lower]
  congr 2
  · change Tensor0SSpace.constInChart (I := I) r x₀
        ((continuousMultilinearMap_basis
          (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper) x₀ =
      basisTensor0S (I := I) (coordinateFrameAt_toBasis (I := I) x₀) upper
    have hxE : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
      mem_baseSet_trivializationAt E (TangentSpace I) x₀
    refine ext0S_basis (I := I) (coordinateFrameAt_toBasis (I := I) x₀) (fun slots => ?_)
    rw [basisTensor0S_component, component0S_apply,
      Tensor0SSpace.constInChart_apply (I := I) r hxE]
    rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
    have hx_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    have hclm :
        (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x₀ =
          (tangentBundleCore I M).coordChange (achart H x₀) (achart H x₀) x₀ := by
      exact TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
        (𝕜 := 𝕜) (I := I) (b₀ := x₀) (b := x₀) hx_src
    have hcoord :
        (tangentBundleCore I M).coordChange (achart H x₀) (achart H x₀) x₀ =
          ContinuousLinearMap.id 𝕜 E := by
      ext v
      exact (tangentBundleCore I M).coordChange_self (achart H x₀) x₀ hx_src v
    rw [hclm]
    rw [hcoord]
    change
      ((continuousMultilinearMap_basis
        (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper)
          (fun i => (Module.finBasis 𝕜 E) (slots i)) =
        if upper = slots then 1 else 0
    rw [← continuousMultilinearMap_basis_repr (Module.finBasis 𝕜 E) r,
      Module.Basis.repr_self, Finsupp.single_apply]
  · funext b
    have hx_src : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
    rw [coordinateFrameAt_toBasis_eq_finBasis (I := I) x₀]
    rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hx_src]
    rw [mfderivWithin_range_extChartAt_symm]
    rfl

omit [IsManifold I 2 M] in
private theorem model_RS_component_eq_coord_component_comp_eventually {r s : ℕ}
    (x₀ : M)
    (T : (x : M) -> TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    let β₀ : Tensor0SModel r 𝕜 E :=
      (continuousMultilinearMap_basis
        (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
    (fun y : E =>
        (tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          r s x₀ T y β₀)
          (fun b => (Module.finBasis 𝕜 E) (lower b))) =ᶠ[
      𝓝[Set.range I] (extChartAt I x₀ x₀)]
    (fun y : E =>
        (T ((extChartAt I x₀).symm y)
          (Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
            (M := M) r x₀ β₀ ((extChartAt I x₀).symm y)))
          (fun b =>
            coordinateFrameAt (I := I) x₀ (lower b)
              ((extChartAt I x₀).symm y))) := by
  intro β₀
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀] with y hy
  unfold tensorRSModelInChart tensorRSModelAt Tensor0SSpace.constInChart
  rw [TensorRSSpace.trivializationAt_apply
    (𝕜 := 𝕜) (I := I) (x₀ := x₀) (x := (extChartAt I x₀).symm y)
    (r := r) (s := s)]
  · congr 2
    funext b
    have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I x₀).map_target hy
    have hy_base : (extChartAt I x₀).symm y ∈ coordinateFrameSet (I := I) x₀ := by
      simpa [coordinateFrameSet, coordinateTrivializationAt] using hy_src
    rw [coordinateFrameAt_apply_of_mem (I := I) hy_base (lower b)]
    rw [TangentBundle.symmL_trivializationAt (I := I) (𝕜 := 𝕜) hy_src]
    rfl
  · have hy_src : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I x₀).map_target hy
    simpa [trivializationAt] using hy_src

set_option backward.isDefEq.respectTransparency false in



omit [IsManifold I 2 M] in
theorem modelDeriv_eq_coordDerivRSAt {r s : ℕ}
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) r s) :
    ModelDerivEqCoordDerivRSAt (I := I) X x₀ (fun x => T x) := by
  classical
  letI := tensorRSBundle_topology (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) r s
  letI := tensorRSBundle_fiber (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) r s
  letI := tensorRSBundle_vector (𝕜 := 𝕜) (E := E) (H := H)
    (I := I) (M := M) r s
  letI : NormedSpace 𝕜 (TensorRSModel r s 𝕜 E) := inferInstance
  intro upper lower
  let z₀ : E := extChartAt I x₀ x₀
  let S : Set E := ((extChartAt I x₀).symm ⁻¹' Set.univ) ∩ Set.range I
  let β₀ : Tensor0SModel r 𝕜 E :=
    (continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) (Module.finBasis 𝕜 E) r) upper
  let u : Fin s -> E := fun b => (Module.finBasis 𝕜 E) (lower b)
  let Tchart : E -> TensorRSModel r s 𝕜 E :=
    fun y => tensorRSModelInChart (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r s x₀ (fun x => T x) y
  let β : (x : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) r x :=
    fun x => Tensor0SSpace.constInChart (𝕜 := 𝕜) (E := E) (H := H)
      (I := I) (M := M) r x₀ β₀ x
  let f : M -> 𝕜 :=
    fun y => (T y (β y))
      (fun b => coordinateFrameAt (I := I) x₀ (lower b) y)
  have hS : S = Set.range I := by
    ext y
    simp [S]
  have hzRange : z₀ ∈ Set.range I := by
    exact extChartAt_target_subset_range x₀ (mem_extChartAt_target (I := I) x₀)
  have hzS : z₀ ∈ S := by
    simpa [hS] using hzRange
  have huniq : UniqueDiffWithinAt 𝕜 S z₀ := by
    simpa [hS, z₀] using I.uniqueDiffOn z₀ hzRange
  have hX :
      VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) z₀ =
        X x₀ := by
    simp only [z₀, VectorField.mpullbackWithin_apply]
    rw [extChartAt_to_inv]
    exact mfderivWithin_extChartAt_symm_inverse_apply (I := I) (x := x₀) (X x₀)
  have hmodel_eventually :
      (fun y : E => (Tchart y β₀) u) =ᶠ[𝓝[S] z₀]
        writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
    have h := model_RS_component_eq_coord_component_comp_eventually
      (I := I) (M := M) (r := r) (s := s) x₀ (fun x => T x) upper lower
    simpa [S, z₀, Tchart, β₀, u, β, f, writtenInExtChartAt] using h
  have hT_model := by
    have h := T.contMDiff x₀
    rw [contMDiffAt_section] at h
    simpa [tensorRSModelAt] using h
  have hsymm :
      ContMDiffWithinAt 𝓘(𝕜, E) I (∞ : WithTop ℕ∞)
        (extChartAt I x₀).symm S z₀ := by
    simpa [S, z₀] using
      contMDiffWithinAt_extChartAt_symm_range_self
        (I := I) (n := (∞ : WithTop ℕ∞)) x₀
  have hT_model_center :
      ContMDiffAt I
        𝓘(𝕜, TensorRSModel r s 𝕜 E)
        (∞ : WithTop ℕ∞)
        (fun x : M =>
          tensorRSModelAt (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
            r s x₀ x (T x))
        ((extChartAt I x₀).symm z₀) := by
    simpa [z₀, extChartAt_to_inv] using hT_model
  have hTchart_cd := by
    have hcomp := ContMDiffAt.comp_contMDiffWithinAt
      (I := 𝓘(𝕜, E)) (I' := I)
      (I'' := 𝓘(𝕜, TensorRSModel r s 𝕜 E))
      (x := z₀) hT_model_center hsymm
    simpa [Tchart, tensorRSModelInChart, Function.comp, z₀] using hcomp
  have hTchart_diff :
      DifferentiableWithinAt 𝕜 Tchart S z₀ := by
    exact hTchart_cd.contDiffWithinAt.differentiableWithinAt (by simp)
  have hscalar_diff :
      DifferentiableWithinAt 𝕜 (fun y : E => (Tchart y β₀) u) S z₀ := by
    have hfun_diff :
        DifferentiableWithinAt 𝕜 (fun y : E => Tchart y β₀) S z₀ :=
      hTchart_diff.clm_apply (differentiableWithinAt_const β₀)
    exact hfun_diff.continuousMultilinear_apply_const u
  have hwritten_diff :
      DifferentiableWithinAt 𝕜
        (writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f) (Set.range I) z₀ := by
    have hscalar_diff_range :
        DifferentiableWithinAt 𝕜 (fun y : E => (Tchart y β₀) u) (Set.range I) z₀ := by
      simpa [hS] using hscalar_diff
    have hmodel_range :
        (fun y : E => (Tchart y β₀) u) =ᶠ[𝓝[Set.range I] z₀]
          writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f := by
      simpa [hS] using hmodel_eventually
    exact (hmodel_range.differentiableWithinAt_iff_of_mem hzRange).mp hscalar_diff_range
  have hf_md : MDifferentiableAt I 𝓘(𝕜, 𝕜) f x₀ := by
    rw [mdifferentiableAt_iff_source_of_mem_source (I := I) (I' := 𝓘(𝕜, 𝕜))
      (x := x₀) (x' := x₀) (mem_chart_source H x₀)]
    rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
    simpa [writtenInExtChartAt, z₀, extChartAt, Function.comp_def] using hwritten_diff
  unfold modelDerivRSAt coordDerivRSAt
  change
    ((fderivWithin 𝕜 Tchart S z₀
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
          (fun x => X x) (Set.range I) z₀)) β₀) u =
      (mfderiv I 𝓘(𝕜, 𝕜) f x₀) (X x₀)
  rw [hX, hf_md.mfderiv]
  have happly₁ :
      (fderivWithin 𝕜 Tchart S z₀ (X x₀)) β₀ =
        fderivWithin 𝕜 (fun y : E => Tchart y β₀) S z₀ (X x₀) := by
    have hconst : DifferentiableWithinAt 𝕜 (fun _ : E => β₀) S z₀ :=
      differentiableWithinAt_const β₀
    have h :=
      congrArg (fun L => L (X x₀))
        (fderivWithin_clm_apply (𝕜 := 𝕜) (s := S) (x := z₀)
          huniq hTchart_diff hconst)
    simpa [fderivWithin_const_apply] using h.symm
  rw [happly₁]
  have hfun_diff :
      DifferentiableWithinAt 𝕜 (fun y : E => Tchart y β₀) S z₀ := by
    exact hTchart_diff.clm_apply (differentiableWithinAt_const β₀)
  have happly₂ :
      (fderivWithin 𝕜 (fun y : E => Tchart y β₀) S z₀ (X x₀)) u =
        fderivWithin 𝕜 (fun y : E => (Tchart y β₀) u) S z₀ (X x₀) := by
    exact (fderivWithin_continuousMultilinear_apply_const_apply
      huniq hfun_diff u (X x₀)).symm
  rw [happly₂]
  have hfd :
      fderivWithin 𝕜 (fun y : E => (Tchart y β₀) u) S z₀ =
        fderivWithin 𝕜 (writtenInExtChartAt I 𝓘(𝕜, 𝕜) x₀ f) S z₀ :=
    hmodel_eventually.fderivWithin_eq_of_mem hzS
  rw [hfd]
  rw [hS]
  rfl


end DifferentialGeometry.Tensor.Coordinates
