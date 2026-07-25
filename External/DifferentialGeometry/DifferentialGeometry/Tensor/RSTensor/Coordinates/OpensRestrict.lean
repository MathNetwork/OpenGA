import DifferentialGeometry.Tensor.RSTensor.Derivation.NablaOnTensors

set_option autoImplicit false
set_option linter.style.longLine false














noncomputable section

namespace DifferentialGeometry

open Bundle Set Topology TopologicalSpace
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in




theorem tangentCoordChange_opens {V : Opens M} [Nonempty V] (p q x : V)
    (hxp : (x : M) ∈ (chartAt H (p : M)).source) :
    (tangentBundleCore I V).coordChange (achart H p) (achart H q) x
      = (tangentBundleCore I M).coordChange (achart H (p : M)) (achart H (q : M)) (x : M) := by
  rw [tangentBundleCore_coordChange_achart, tangentBundleCore_coordChange_achart]
  have hsrc : x ∈ (chartAt H p).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact hxp
  have hval : extChartAt I p x = extChartAt I (p : M) (x : M) := rfl
  have hev : (extChartAt I q ∘ (extChartAt I p).symm)
      =ᶠ[𝓝[Set.range I] extChartAt I (p : M) (x : M)]
      (extChartAt I (q : M) ∘ (extChartAt I (p : M)).symm) := by
    rw [← hval]
    filter_upwards [(chartAt H p).extend_target_mem_nhdsWithin (I := I) hsrc] with y hy
    have hy' : I.symm y ∈ (chartAt H p).target := by
      rw [OpenPartialHomeomorph.extend_target] at hy
      exact hy.1
    have hw : Subtype.val ((chartAt H p).symm (I.symm y))
        = (chartAt H (p : M)).symm (I.symm y) := by
      rw [TopologicalSpace.Opens.chartAt_eq] at hy' ⊢
      exact OpenPartialHomeomorph.subtypeRestr_symm_apply _ _ hy'
    show extChartAt I q ((extChartAt I p).symm y)
        = extChartAt I (q : M) ((extChartAt I (p : M)).symm y)
    have hsy : (extChartAt I p).symm y = ((chartAt H p).symm (I.symm y) : V) := rfl
    have hsy' : (extChartAt I (p : M)).symm y
        = (chartAt H (p : M)).symm (I.symm y) := rfl
    rw [hsy, hsy']
    show I (chartAt H q ((chartAt H p).symm (I.symm y)))
        = I (chartAt H (q : M) ((chartAt H (p : M)).symm (I.symm y)))
    rw [← hw]
    rfl
  exact hev.fderivWithin_eq
    (hev.eq_of_nhdsWithin ⟨(chartAt H (p : M)) (x : M), rfl⟩)

omit [CompleteSpace E] in






theorem tensor0SModelAt_opens (s : ℕ) {V : Opens M} [Nonempty V] (p x : V)
    (hxp : (x : M) ∈ (chartAt H (p : M)).source)
    (A : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := V) s x) :
    TensorLieDeriv.tensor0SModelAt (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := V) s p x A
      = TensorLieDeriv.tensor0SModelAt (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
          s (p : M) (x : M) A := by
  have hsrc : x ∈ (chartAt H p).source := by
    rw [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]
    exact hxp
  have hL : (trivializationAt E (TangentSpace I (M := V)) p).symmL ℝ x
      = (tangentBundleCore I V).coordChange (achart H p) (achart H x) x :=
    TangentBundle.symmL_trivializationAt_eq_core hsrc
  have hR : (trivializationAt E (TangentSpace I (M := M)) (p : M)).symmL ℝ (x : M)
      = (tangentBundleCore I M).coordChange (achart H (p : M)) (achart H (x : M)) (x : M) :=
    TangentBundle.symmL_trivializationAt_eq_core hxp
  change A.compContinuousLinearMap
      (fun _ => (trivializationAt E (TangentSpace I (M := V)) p).symmL ℝ x)
    = ContinuousMultilinearMap.compContinuousLinearMap A
      (fun _ => (trivializationAt E (TangentSpace I (M := M)) (p : M)).symmL ℝ (x : M))
  rw [hL, hR, tangentCoordChange_opens (I := I) p x x hxp]

end DifferentialGeometry

namespace DifferentialGeometry

open Bundle Set Topology TopologicalSpace
open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false in






noncomputable def restrictOpen0S {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (s : ℕ) [IsManifold I 1 M] {V : Opens M} [Nonempty V]
    (δ : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := V) (n := (∞ : WithTop ℕ∞)) s :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := V) s
  { toFun := fun x => δ (x : M)
    contMDiff_toFun := by
      intro x₀
      rw [Bundle.contMDiffAt_section]
      have hM := δ.contMDiff_toFun.contMDiffAt (x := (x₀ : M))
      rw [Bundle.contMDiffAt_section] at hM
      have hval : ContMDiffAt I I (∞ : WithTop ℕ∞) (Subtype.val : V → M) x₀ :=
        (contMDiff_subtype_val (I := I) (U := V)).contMDiffAt
      have hcomp := hM.comp x₀ hval
      refine hcomp.congr_of_eventuallyEq ?_
      have hnb : {x : V | (x : M) ∈ (chartAt H (x₀ : M)).source} ∈ 𝓝 x₀ :=
        ((chartAt H (x₀ : M)).open_source.preimage continuous_subtype_val).mem_nhds
          (mem_chart_source H (x₀ : M))
      filter_upwards [hnb] with x hx
      exact tensor0SModelAt_opens s x₀ x hx (δ (x : M)) }


end DifferentialGeometry
