import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Derivation
import DifferentialGeometry.Tensor.RSTensor.LocalFrameRegularity
import DifferentialGeometry.Tensor.RSTensor.Derivation.NablaOnTensors






namespace Tensor0SBundle

open Bundle Set TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]

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
theorem tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M => (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    DifferentiableWithinAt 𝕜
      (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
      (Set.range I) (extChartAt I x₀ x₀) := by
  exact (tangentFieldModelInChart_contDiffWithinAt_center_of_contMDiffAt
    (I := I) V x₀ hV).differentiableWithinAt (by simp)

omit [IsManifold I 2 M] in
theorem tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M => (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀)
    (i : Fin (Module.finrank 𝕜 E)) :
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

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
omit [IsManifold I ∞ M] in
private theorem tangentFieldModelInChart_contDiffWithinAt_center_of_contMDiffAt_one
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (1 : WithTop ℕ∞)
      (fun p : M => (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    ContDiffWithinAt 𝕜 (1 : WithTop ℕ∞)
      (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
      (Set.range I) (extChartAt I x₀ x₀) := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hx : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hcoord :
      ContMDiffAt I 𝓘(𝕜, E) (1 : WithTop ℕ∞)
        (fun p : M => (e ⟨p, V p⟩).2) x₀ :=
    (e.contMDiffAt_section_iff hx).mp hV
  have hsymm :
      ContMDiffWithinAt 𝓘(𝕜, E) I (1 : WithTop ℕ∞)
        (extChartAt I x₀).symm (Set.range I) (extChartAt I x₀ x₀) := by
    simpa using
      contMDiffWithinAt_extChartAt_symm_range_self
        (I := I) (n := (1 : WithTop ℕ∞)) x₀
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  have hcoord_center :
      ContMDiffAt I 𝓘(𝕜, E) (1 : WithTop ℕ∞)
        (fun p : M => (e ⟨p, V p⟩).2)
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    simpa [hcenter] using hcoord
  have hfixed :
      ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E) (1 : WithTop ℕ∞)
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
      ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E) (1 : WithTop ℕ∞)
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

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
omit [IsManifold I ∞ M] in
theorem tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt_one
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (1 : WithTop ℕ∞)
      (fun p : M => (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    DifferentiableWithinAt 𝕜
      (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V)
      (Set.range I) (extChartAt I x₀ x₀) := by
  exact (tangentFieldModelInChart_contDiffWithinAt_center_of_contMDiffAt_one
    (I := I) V x₀ hV).differentiableWithinAt (by norm_num)

omit [IsManifold I ∞ M] in
theorem tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt_one
    (V : (x : M) -> TangentSpace I x) (x₀ : M)
    (hV : ContMDiffAt I (I.prod 𝓘(𝕜, E)) (1 : WithTop ℕ∞)
      (fun p : M => (⟨p, V p⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀)
    (i : Fin (Module.finrank 𝕜 E)) :
    MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M =>
        (Module.finBasis 𝕜 E).coord i
          (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ V
            (extChartAt I x₀ p))) x₀ := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hx : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hcoord :
      ContMDiffAt I 𝓘(𝕜, E) (1 : WithTop ℕ∞)
        (fun p : M => (e ⟨p, V p⟩).2) x₀ :=
    (e.contMDiffAt_section_iff hx).mp hV
  have hscalar :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (1 : WithTop ℕ∞)
        (fun p : M => (Module.finBasis 𝕜 E).coord i ((e ⟨p, V p⟩).2)) x₀ := by
    have hlin :
        ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
          (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord i)) :=
      (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord i)).contMDiff
    exact (hlin.of_le (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))).contMDiffAt.comp
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
  exact (hscalar.congr_of_eventuallyEq heq).mdifferentiableAt (by norm_num)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem tangentConst_covariantDeriv_apply_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (v : E) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, (cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v) p) (X p)⟩ :
          TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  let Xinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => X p, X.contMDiff.of_le (by simp)⟩
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (by simp)
  have hW_on :
      CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
        (T% (fun p : M =>
          (cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ v) p) (Xinf p))) := by
    simpa [e, Xinf] using
      (covariantDerivative_tangentConst_apply_contMDiffOn_baseSet
        (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        cov hcov Xinf x₀ v)
  exact ((hW_on x₀ hx₀).contMDiffAt (e.open_baseSet.mem_nhds hx₀)).of_le
    (by simp : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))

set_option backward.isDefEq.respectTransparency false in


theorem tensor0S_eval_tangentConst_covariantDerivative_slot_contMDiffAt
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin s -> Fin (Module.finrank 𝕜 E)) (a : Fin s) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        α p
          (Function.update
            (fun b : Fin s =>
              tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
                ((Module.finBasis 𝕜 E) (slots b)) p)
            a
            ((cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) (slots a))) p) (X p))))
      x₀ := by
  let αinf : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s :=
    ⟨fun p : M => α p, α.contMDiff.of_le (by simp)⟩
  let W : (p : M) -> TangentSpace I p :=
    fun p : M =>
      (cov (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
        ((Module.finBasis 𝕜 E) (slots a))) p) (X p)
  have hW :
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun p : M => (⟨p, W p⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
        x₀ := by
    simpa [W] using
      tangentConst_covariantDeriv_apply_contMDiffAt
        (I := I) cov hcov X x₀ ((Module.finBasis 𝕜 E) (slots a))
  have hframe :
      ∀ i : Fin s,
        ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
          (fun p : M =>
            (⟨p,
              Function.update
                (fun b : Fin s =>
                  tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
                    ((Module.finBasis 𝕜 E) (slots b)) p)
                a
                (W p) i⟩ :
              TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    intro i
    by_cases hi : i = a
    · subst hi
      simpa using hW
    · let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
      have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
      have hbase_on :
          CMDiff[e.baseSet] (∞ : WithTop ℕ∞)
            (T% (tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) (slots i)) :
              (p : M) -> TangentSpace I p)) := by
        simpa [e] using
          (tangentConstInChart_contMDiffOn_baseSet
            (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
            x₀ ((Module.finBasis 𝕜 E) (slots i)))
      have hbase := (hbase_on x₀ hx₀).contMDiffAt (e.open_baseSet.mem_nhds hx₀)
      simpa [Function.update, hi] using hbase
  have hEval := TensorMultilinear.contMDiffAt_section_apply_gen
    (I := I) (M := M) (n := s) (x₀ := x₀)
    (T := fun p : M => αinf p) αinf.contMDiff.contMDiffAt
    (v := fun i : Fin s =>
      fun p : M =>
        Function.update
          (fun b : Fin s =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) (slots b)) p)
          a
          (W p) i)
    (hv := hframe)
  simpa [αinf, W, Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    using hEval

set_option backward.isDefEq.respectTransparency false in
theorem localCovariantDerivTensor0SAt_constInChart_eval_tangentConstInChart_contMDiffAt
    {r : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (β : Tensor0SModel r 𝕜 E)
    (slots : Fin r -> Fin (Module.finrank 𝕜 E)) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X
          (fun y : M => Tensor0SSpace.constInChart
            (𝕜 := 𝕜) (I := I) (M := M) r x₀ β y) p)
          (fun a : Fin r =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) (slots a)) p)) x₀ := by
  let βsec : (p : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r p :=
    fun p : M => Tensor0SSpace.constInChart
      (𝕜 := 𝕜) (I := I) (M := M) r x₀ β p
  let V : Fin r -> (p : M) -> TangentSpace I p :=
    fun a => tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
      ((Module.finBasis 𝕜 E) (slots a))
  let pair : M -> 𝕜 := fun p : M => βsec p (fun a : Fin r => V a p)
  let Xinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => X p, X.contMDiff.of_le (by simp)⟩
  have hβsec : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
      (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p, βsec p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x₀ := by
    simpa [βsec] using
      tensor0SConstInChart_contMDiffAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) x₀ β
  have hV :
      ∀ a : Fin r,
        ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
          (fun p : M => (⟨p, V a p⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
          x₀ := by
    intro a
    let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
    have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
    have hconst_on :
        CMDiff[e.baseSet] (∞ : WithTop ℕ∞) (T% (V a)) := by
      simpa [e, V] using
        (tangentConstInChart_contMDiffOn_baseSet
          (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
          x₀ ((Module.finBasis 𝕜 E) (slots a)))
    exact (hconst_on x₀ hx₀).contMDiffAt (e.open_baseSet.mem_nhds hx₀)
  have hpair : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair x₀ := by
    have hEval := TensorMultilinear.contMDiffAt_section_apply_gen
      (I := I) (M := M) (n := r) (x₀ := x₀)
      (T := βsec) hβsec
      (v := V) hV
    simpa [pair, Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
      using hEval
  have hderiv :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => extDerivFun (I := I) pair p (X p)) x₀ := by
    simpa [Xinf] using DifferentialGeometry.extDerivFun_apply_contMDiffAt I hpair Xinf
  have hcorr_sum :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          ∑ a : Fin r,
            βsec p
              (Function.update
                (fun b : Fin r => V b p)
                a
                ((cov (V a) p) (X p)))) x₀ := by
    apply ContMDiffAt.sum
    intro a _
    let W : (p : M) -> TangentSpace I p := fun p : M => (cov (V a) p) (X p)
    have hW :
        ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
          (fun p : M => (⟨p, W p⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
          x₀ := by
      simpa [W, V] using
        tangentConst_covariantDeriv_apply_contMDiffAt
          (I := I) cov hcov X x₀ ((Module.finBasis 𝕜 E) (slots a))
    have hframe :
        ∀ i : Fin r,
          ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
            (fun p : M =>
              (⟨p, Function.update (fun b : Fin r => V b p) a (W p) i⟩ :
                TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
      intro i
      by_cases hi : i = a
      · subst hi
        simpa using hW
      · simpa [Function.update, hi] using hV i
    have hEval := TensorMultilinear.contMDiffAt_section_apply_gen
      (I := I) (M := M) (n := r) (x₀ := x₀)
      (T := βsec) hβsec
      (v := fun i : Fin r => fun p : M =>
        Function.update (fun b : Fin r => V b p) a (W p) i)
      (hv := hframe)
    simpa [W, Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
      using hEval
  have hmain :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          extDerivFun (I := I) pair p (X p) -
            ∑ a : Fin r,
              βsec p
                (Function.update
                  (fun b : Fin r => V b p)
                  a
                  ((cov (V a) p) (X p)))) x₀ :=
    hderiv.sub hcorr_sum
  refine hmain.congr_of_eventuallyEq ?_
  let eTan := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let eβ := trivializationAt (Tensor0SModel r 𝕜 E)
    (fun p : M => Tensor0SSpace r I p) x₀
  have hx₀Tan : x₀ ∈ eTan.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have hx₀β : x₀ ∈ eβ.baseSet := by
    simpa [eβ] using
      (mem_baseSet_trivializationAt
        (Tensor0SModel r 𝕜 E) (fun p : M => Tensor0SSpace r I p) x₀)
  filter_upwards [eTan.open_baseSet.mem_nhds hx₀Tan,
    eβ.open_baseSet.mem_nhds hx₀β] with p hpTan hpβ
  have hβ_p : ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E))
      (∞ : WithTop ℕ∞)
      (fun y : M =>
        (⟨y, βsec y⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun y : M => Tensor0SSpace r I y))) p := by
    simpa [βsec] using
      tensor0SConstInChart_contMDiffAt_of_mem
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) x₀ β hpβ
  have hV_p :
      ∀ a : Fin r,
        ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
          (fun y : M => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M -> Type _)))
          p := by
    intro a
    have hconst_on :
        CMDiff[eTan.baseSet] (∞ : WithTop ℕ∞) (T% (V a)) := by
      simpa [eTan, V] using
        (tangentConstInChart_contMDiffOn_baseSet
          (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
          x₀ ((Module.finBasis 𝕜 E) (slots a)))
    exact (hconst_on p hpTan).contMDiffAt (eTan.open_baseSet.mem_nhds hpTan)
  have hpair_md : MDifferentiableAt I 𝓘(𝕜, 𝕜) pair p := by
    have hpair_p : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair p := by
      have hEval := TensorMultilinear.contMDiffAt_section_apply_gen
        (I := I) (M := M) (n := r) (x₀ := p)
        (T := βsec) hβ_p
        (v := V) hV_p
      simpa [pair, Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
        using hEval
    exact hpair_p.mdifferentiableAt (by simp)
  have hβmodel_p :
      DifferentiableWithinAt 𝕜
        (tensor0SModelInChart (𝕜 := 𝕜) (E := E) (H := H) (I := I)
          (M := M) r p βsec)
        (Set.range I) (extChartAt I p p) :=
    tensor0SModelInChart_differentiableWithinAt_center_of_contMDiffAt
      (I := I) βsec p hβ_p
  have hV_md : ∀ a : Fin r, MDiffAt (T% (V a)) p :=
    fun a => (hV_p a).mdifferentiableAt (by simp)
  have hVmodel_p : ∀ a : Fin r,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) p (V a))
        (Set.range I) (extChartAt I p p) :=
    fun a =>
      tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
        (I := I) (V a) p (hV_p a)
  have hcoord_p : ∀ a : Fin r, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun q : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) p (V a)
              (extChartAt I p q))) p :=
    fun a i =>
      tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
        (I := I) (V a) p (hV_p a) i
  rw [localCovariantDerivTensor0SAt_eval_moving_raw
    (I := I) cov X βsec V p hpair_md hβmodel_p hV_md hVmodel_p hcoord_p]

set_option backward.isDefEq.respectTransparency false in
theorem localCovariantDerivTensor0SAt_constInChart_contMDiffAt
    {r : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (x₀ : M) (β : Tensor0SModel r 𝕜 E) :
    ContMDiffAt I (I.prod 𝓘(𝕜, Tensor0SModel r 𝕜 E)) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (⟨p,
          localCovariantDerivTensor0SAt
            (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X
            (fun y : M => Tensor0SSpace.constInChart
              (𝕜 := 𝕜) (I := I) (M := M) r x₀ β y) p⟩ :
          TotalSpace (Tensor0SModel r 𝕜 E)
            (fun p : M => Tensor0SSpace r I p))) x₀ := by
  let F : (p : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) r p :=
    fun p : M =>
      localCovariantDerivTensor0SAt
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X
        (fun y : M => Tensor0SSpace.constInChart
          (𝕜 := 𝕜) (I := I) (M := M) r x₀ β y) p
  let e := trivializationAt (Tensor0SModel r 𝕜 E)
    (fun p : M => Tensor0SSpace r I p) x₀
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  rw [contMDiffAt_section]
  let g : M -> Tensor0SModel r 𝕜 E := fun p : M => (e ⟨p, F p⟩).2
  change ContMDiffAt I 𝓘(𝕜, Tensor0SModel r 𝕜 E) (∞ : WithTop ℕ∞) g x₀
  let B := continuousMultilinearMap_basis (𝕜 := 𝕜) (F := E) b r
  rw [show g = fun p : M => B.equivFun.symm (B.equivFun (g p)) from
      funext fun p => (B.equivFun.symm_apply_apply (g p)).symm]
  exact (B.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt).comp x₀
    (contMDiffAt_pi_space.mpr fun σ => by
      have hcoeff :=
        localCovariantDerivTensor0SAt_constInChart_eval_tangentConstInChart_contMDiffAt
          (I := I) cov hcov X x₀ β σ
      refine hcoeff.congr_of_eventuallyEq ?_
      let eTan := trivializationAt E (TangentSpace I : M -> Type _) x₀
      have hx₀Tan : x₀ ∈ eTan.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
      filter_upwards [eTan.open_baseSet.mem_nhds hx₀Tan] with p hp
      change B.repr (g p) σ =
        (localCovariantDerivTensor0SAt
          (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r cov X
          (fun y : M => Tensor0SSpace.constInChart
            (𝕜 := 𝕜) (I := I) (M := M) r x₀ β y) p)
          (fun a : Fin r =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) (σ a)) p)
      rw [continuousMultilinearMap_basis_repr]
      change ((trivializationAt (Tensor0SModel r 𝕜 E)
          (Bundle.continuousMultilinearMap 𝕜 r E (TangentSpace I : M -> Type _)) x₀
          ⟨p, F p⟩).2)
          (fun a : Fin r => b (σ a)) =
        F p
          (fun a : Fin r =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b (σ a)) p)
      change (F p).compContinuousLinearMap
          (fun _ : Fin r =>
            (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 p)
          (fun a : Fin r => b (σ a)) =
        F p
          (fun a : Fin r =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b (σ a)) p)
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      congr)

set_option backward.isDefEq.respectTransparency false in





theorem nabla0SFun_eval_smooth_slots {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α x₀) (fun a : Fin s => V a x₀) =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀) -
        ∑ a : Fin s,
          α x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (fun p : M => V a p) x₀) (X x₀))) := by
  let W : Fin s -> (p : M) -> TangentSpace I p := fun a p => V a p
  have hV_at : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun y : M => (⟨y, W a y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    intro a
    exact (V a).contMDiff.contMDiffAt
  have hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => α p (fun a : Fin s => W a p)) x₀ := by
    have hpair_top :
        ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
          (fun p : M => α p (fun a : Fin s => W a p)) x₀ := by
      have hα_top := α.contMDiff x₀
      have hα := hα_top.of_le
        (by simp : (∞ : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
      have hEval := TensorMultilinear.contMDiffAt_section_apply_gen
        (I := I) (M := M) (n := s) (x₀ := x₀)
        (T := fun y : M => α y) hα
        (v := fun a : Fin s => W a)
        (hv := hV_at)
      simpa [W, Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
        using hEval
    exact hpair_top.mdifferentiableAt (by simp)
  have hV_md : ∀ a : Fin s, MDiffAt (T% (W a)) x₀ :=
    fun a => (hV_at a).mdifferentiableAt (by simp)
  have hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (W a))
        (Set.range I) (extChartAt I x₀ x₀) :=
    fun a =>
      tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
        (I := I) (W a) x₀ (hV_at a)
  have hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (W a)
              (extChartAt I x₀ p))) x₀ :=
    fun a i =>
      tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
        (I := I) (W a) x₀ (hV_at a) i
  simpa [W] using
    nabla0SFun_eval_coordFrame_moving_raw
      (I := I) cov X W α x₀ hpair hV_md hVmodel hcoord

set_option backward.isDefEq.respectTransparency false in


omit [IsManifold I 2 M] in
theorem tensor0SField_eval_smooth_slots_contMDiffAt {s : ℕ}
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x₀ : M) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M => α p (fun a : Fin s => V a p)) x₀ := by
  have hα_top := α.contMDiff x₀
  have hV_top : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun y : M =>
          (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀ := by
    intro a
    exact (V a).contMDiff.contMDiffAt
  have hEval := TensorMultilinear.contMDiffAt_section_apply_gen
    (I := I) (M := M) (n := s) (x₀ := x₀)
    (T := fun y : M => α y) hα_top
    (v := fun a : Fin s => fun y : M => V a y)
    (hv := hV_top)
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    using hEval

set_option backward.isDefEq.respectTransparency false in


omit [IsManifold I 2 M] in
theorem tensor0SField_eval_C1_slots_contMDiffAt_one {s : ℕ}
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (V : Fin s -> (x : M) -> TangentSpace I x)
    (x₀ : M)
    (hV_at : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (1 : WithTop ℕ∞)
      (fun p : M => α p (fun a : Fin s => V a p)) x₀ := by
  have hα_top := α.contMDiff x₀
  have hα_one := hα_top.of_le
    (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hEval := TensorMultilinear.contMDiffAt_section_apply_one
    (I := I) (M := M) (n := s) (x₀ := x₀)
    (T := fun y : M => α y) hα_one
    (v := fun a : Fin s => V a)
    (hv := hV_at)
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply]
    using hEval

set_option backward.isDefEq.respectTransparency false in

omit [IsManifold I 2 M] in
theorem tensor0SField_eval_C1_slots_mdiffAt {s : ℕ}
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (V : Fin s -> (x : M) -> TangentSpace I x)
    (x₀ : M)
    (hV_at : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => α p (fun a : Fin s => V a p)) x₀ :=
  (tensor0SField_eval_C1_slots_contMDiffAt_one
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    α V x₀ hV_at).mdifferentiableAt (by norm_num)

set_option backward.isDefEq.respectTransparency false in

theorem nabla0SFun_eval_C1_slots {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin s -> (x : M) -> TangentSpace I x)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M)
    (hV_at : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (1 : WithTop ℕ∞)
        (fun y : M => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) x₀) :
    (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      s cov X α x₀) (fun a : Fin s => V a x₀) =
      extDerivFun (I := I) (fun p : M => α p (fun a : Fin s => V a p))
        x₀ (X x₀) -
        ∑ a : Fin s,
          α x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (V a) x₀) (X x₀))) := by
  have hpair : MDifferentiableAt I 𝓘(𝕜, 𝕜)
      (fun p : M => α p (fun a : Fin s => V a p)) x₀ := by
    exact tensor0SField_eval_C1_slots_mdiffAt
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) α V x₀ hV_at
  have hV_md : ∀ a : Fin s, MDiffAt (T% (V a)) x₀ :=
    fun a => (hV_at a).mdifferentiableAt (by norm_num)
  have hVmodel : ∀ a : Fin s,
      DifferentiableWithinAt 𝕜
        (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a))
        (Set.range I) (extChartAt I x₀ x₀) :=
    fun a =>
      tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt_one
        (I := I) (V a) x₀ (hV_at a)
  have hcoord : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
      MDifferentiableAt I 𝓘(𝕜, 𝕜)
        (fun p : M =>
          (Module.finBasis 𝕜 E).coord i
            (tangentFieldModelInChart (𝕜 := 𝕜) (I := I) x₀ (V a)
              (extChartAt I x₀ p))) x₀ :=
    fun a i =>
      tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt_one
        (I := I) (V a) x₀ (hV_at a) i
  exact
    nabla0SFun_eval_coordFrame_moving_raw
      (I := I) cov X V α x₀ hpair hV_md hVmodel hcoord

set_option backward.isDefEq.respectTransparency false in


theorem nabla0SFun_eval_tangentConstInChart_contMDiffAt
    {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (slots : Fin s -> Fin (Module.finrank 𝕜 E)) :
    ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
      (fun p : M =>
        (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
          s cov X α p)
          (fun a : Fin s =>
            tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
              ((Module.finBasis 𝕜 E) (slots a)) p)) x₀ := by
  let V : Fin s -> (p : M) -> TangentSpace I p :=
    fun a => tangentConstInChart (𝕜 := 𝕜) (I := I) x₀
      ((Module.finBasis 𝕜 E) (slots a))
  let pair : M -> 𝕜 := fun p : M => α p (fun a : Fin s => V a p)
  let Xinf : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    ⟨fun p : M => X p, X.contMDiff.of_le (by simp)⟩
  have hpair : ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞) pair x₀ := by
    simpa [pair, V] using
      tensor0S_eval_tangentConstInChart_contMDiffAt
        (I := I) α x₀ slots
  have hderiv :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M => extDerivFun (I := I) pair p (X p)) x₀ := by
    simpa [Xinf] using DifferentialGeometry.extDerivFun_apply_contMDiffAt I hpair Xinf
  have hcorr_sum :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          ∑ a : Fin s,
            α p
              (Function.update
                (fun b : Fin s => V b p)
                a
                ((cov (V a) p) (X p)))) x₀ := by
    apply ContMDiffAt.sum
    intro a _
    simpa [V] using
      tensor0S_eval_tangentConst_covariantDerivative_slot_contMDiffAt
        (I := I) cov hcov X α x₀ slots a
  have hmain :
      ContMDiffAt I 𝓘(𝕜, 𝕜) (∞ : WithTop ℕ∞)
        (fun p : M =>
          extDerivFun (I := I) pair p (X p) -
            ∑ a : Fin s,
              α p
                (Function.update
                  (fun b : Fin s => V b p)
                  a
                  ((cov (V a) p) (X p)))) x₀ :=
    hderiv.sub hcorr_sum
  refine hmain.congr_of_eventuallyEq ?_
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  filter_upwards [e.open_baseSet.mem_nhds hx₀] with p hp
  have hV_at : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(𝕜, E)) (∞ : WithTop ℕ∞)
        (fun y : M => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M -> Type _))) p := by
    intro a
    have hconst_on :
        CMDiff[e.baseSet] (∞ : WithTop ℕ∞) (T% (V a)) := by
      simpa [e, V] using
        (tangentConstInChart_contMDiffOn_baseSet
          (𝕜 := 𝕜) (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
          x₀ ((Module.finBasis 𝕜 E) (slots a)))
    exact (hconst_on p hp).contMDiffAt (e.open_baseSet.mem_nhds hp)
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
  have hcoord_p : ∀ a : Fin s, ∀ i : Fin (Module.finrank 𝕜 E),
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



theorem nabla0S_reg (s : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) :
    Nabla0SRegular (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s cov X α := by
  letI := tensor0SBundle_topology (𝕜 := 𝕜) (E := E) (H := H) (I := I)
    (M := M) s
  let F : (p : M) -> Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I)
      (M := M) s p :=
    fun p : M =>
      nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α p
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  have hsec :
      ContMDiff I (I.prod 𝓘(𝕜, Tensor0SModel s 𝕜 E)) (∞ : WithTop ℕ∞)
        (fun p : M =>
          (⟨p, F p⟩ :
            TotalSpace (Tensor0SModel s 𝕜 E) (fun p : M => Tensor0SSpace s I p))) := by
    refine (contMDiff_multilinearSection_iff_coord (TangentSpace I)
      (∞ : WithTop ℕ∞) b F).mpr ?_
    intro σ x₀
    have hcoeff :=
      nabla0SFun_eval_tangentConstInChart_contMDiffAt
        (I := I) cov hcov X α x₀ σ
    refine hcoeff.congr_of_eventuallyEq ?_
    let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
    have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
    filter_upwards [e.open_baseSet.mem_nhds hx₀] with p hp
    rw [continuousMultilinearMap_basis_repr]
    change ((trivializationAt (Tensor0SModel s 𝕜 E)
        (Bundle.continuousMultilinearMap 𝕜 s E (TangentSpace I : M -> Type _)) x₀
        ⟨p, F p⟩).2)
        (fun a : Fin s => b (σ a)) =
      (nabla0SFun (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
        s cov X α p)
        (fun a : Fin s =>
          tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b (σ a)) p)
    change (F p).compContinuousLinearMap
        (fun _ : Fin s =>
          (trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL 𝕜 p)
        (fun a : Fin s => b (σ a)) =
      F p
        (fun a : Fin s =>
          tangentConstInChart (𝕜 := 𝕜) (I := I) x₀ (b (σ a)) p)
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr
  exact hsec

end Tensor0SBundle
