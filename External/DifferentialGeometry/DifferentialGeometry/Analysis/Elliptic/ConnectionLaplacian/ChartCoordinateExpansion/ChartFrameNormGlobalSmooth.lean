import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import DifferentialGeometry.Analysis.Integration.Measure.RiemannianMeasure
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.InnerBounds.InnerLowerBound


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [ChartedSpace H M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma locallyCompactSpace_M (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] : LocallyCompactSpace M := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  exact ChartedSpace.locallyCompactSpace H M

omit [NeZero (Module.finrank ℝ E)] [ChartedSpace H M] [CompactSpace M] [T2Space M] in
private lemma regularSpace_M (I : ModelWithCorners ℝ E H)
    [ChartedSpace H M] [T2Space M] : RegularSpace M := by
  haveI : LocallyCompactSpace M := locallyCompactSpace_M (E := E) (H := H) (M := M) I
  haveI : WeaklyLocallyCompactSpace M := inferInstance
  haveI : R1Space M := T2Space.r1Space
  infer_instance

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pouTsupport_subset_chartAt_source (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H α).source :=
  (chartAtlasPOU_isSubordinate I M) α

omit [ChartedSpace H M] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private lemma exists_open_closure_subset_open_of_isCompact
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [T2Space M]
    {K U : Set M} (hK : IsCompact K) (hU_open : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ V : Set M, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U := by
  haveI : RegularSpace M := regularSpace_M (E := E) (H := H) (M := M) I
  have hU_nhdsSet : U ∈ 𝓝ˢ K := hU_open.mem_nhdsSet.mpr hKU
  exact hK.exists_isOpen_closure_subset hU_nhdsSet

omit [ChartedSpace H M] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_open_closure_open_closure_subset_open_of_isCompact
    (I : ModelWithCorners ℝ E H) [ChartedSpace H M] [T2Space M]
    {K U : Set M} (hK : IsCompact K) (hU_open : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ V₁ V₂ : Set M, IsOpen V₁ ∧ IsOpen V₂ ∧
      K ⊆ V₁ ∧ closure V₁ ⊆ V₂ ∧ closure V₂ ⊆ U := by
  obtain ⟨V₁, hV₁_open, hKV₁, hclos_V₁_U⟩ :=
    exists_open_closure_subset_open_of_isCompact (E := E) (H := H)
      (M := M) I hK hU_open hKU
  have hclos_V₁_compact : IsCompact (closure V₁) := isClosed_closure.isCompact
  obtain ⟨V₂, hV₂_open, hclos_V₁_V₂, hclos_V₂_U⟩ :=
    exists_open_closure_subset_open_of_isCompact (E := E) (H := H)
      (M := M) I hclos_V₁_compact hU_open hclos_V₁_U
  refine ⟨V₁, V₂, hV₁_open, hV₂_open, hKV₁, hclos_V₁_V₂, hclos_V₂_U⟩

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_globalBump_data (α : M) :
    ∃ V₁ V₂ : Set M, ∃ ψ : M → ℝ,
      IsOpen V₁ ∧ IsOpen V₂ ∧
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆ V₁ ∧
      closure V₁ ⊆ V₂ ∧
      closure V₂ ⊆ (chartAt H α).source ∧
      ContMDiff I 𝓘(ℝ) ∞ ψ ∧
      range ψ ⊆ Icc (0 : ℝ) 1 ∧
      (∀ x, x ∈ closure V₁ ↔ ψ x = 1) ∧
      (∀ x, x ∈ (V₂ᶜ : Set M) ↔ ψ x = 0) := by
  classical
  obtain ⟨V₁, V₂, hV₁_open, hV₂_open, hKV₁, hclos_V₁_V₂, hclos_V₂_src⟩ :=
    exists_open_closure_open_closure_subset_open_of_isCompact
      (E := E) (H := H) (M := M) I
      (pouTsupport_isCompact (I := I) (M := M) α)
      ((chartAt H α).open_source)
      (pouTsupport_subset_chartAt_source (I := I) (M := M) α)
  set s : Set M := V₂ᶜ
  set t : Set M := closure V₁
  have hs_closed : IsClosed s := isClosed_compl_iff.mpr hV₂_open
  have ht_closed : IsClosed t := isClosed_closure
  have hdisjoint : Disjoint s t := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    refine ⟨?_, fun hx => (Set.notMem_empty x hx).elim⟩
    rintro ⟨hx_s, hx_t⟩
    have hx_V₂ : x ∈ V₂ := hclos_V₁_V₂ hx_t
    have hx_notV₂ : x ∉ V₂ := hx_s
    exact (hx_notV₂ hx_V₂).elim
  have h_urysohn :
      ∃ f : M → ℝ,
        ContMDiff I 𝓘(ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
        range f ⊆ Icc (0 : ℝ) 1 ∧
        (∀ x, x ∈ s ↔ f x = 0) ∧
        (∀ x, x ∈ t ↔ f x = 1) :=
    exists_contMDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞)) I
      hs_closed ht_closed hdisjoint
  obtain ⟨ψ, hψ_smooth, hψ_range, hψ_s, hψ_t⟩ := h_urysohn
  have hψ_smooth' : ContMDiff I 𝓘(ℝ) ∞ ψ := by
    have : ((⊤ : ℕ∞) : WithTop ℕ∞) = (∞ : WithTop ℕ∞) := rfl
    rw [this] at hψ_smooth
    exact hψ_smooth
  exact ⟨V₁, V₂, ψ, hV₁_open, hV₂_open, hKV₁, hclos_V₁_V₂, hclos_V₂_src,
    hψ_smooth', hψ_range, hψ_t, hψ_s⟩

private noncomputable def globalBumpV₁ (α : M) : Set M :=
  Classical.choose (exists_globalBump_data (I := I) (M := M) α)

private noncomputable def globalBumpV₂ (α : M) : Set M :=
  Classical.choose (Classical.choose_spec
    (exists_globalBump_data (I := I) (M := M) α))

private noncomputable def globalBumpψ (α : M) : M → ℝ :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (exists_globalBump_data (I := I) (M := M) α)))

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma globalBumpData_spec (α : M) :
    IsOpen (globalBumpV₁ (I := I) (M := M) α) ∧
      IsOpen (globalBumpV₂ (I := I) (M := M) α) ∧
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
        globalBumpV₁ (I := I) (M := M) α ∧
      closure (globalBumpV₁ (I := I) (M := M) α) ⊆
        globalBumpV₂ (I := I) (M := M) α ∧
      closure (globalBumpV₂ (I := I) (M := M) α) ⊆ (chartAt H α).source ∧
      ContMDiff I 𝓘(ℝ) ∞ (globalBumpψ (I := I) (M := M) α) ∧
      range (globalBumpψ (I := I) (M := M) α) ⊆ Icc (0 : ℝ) 1 ∧
      (∀ x, x ∈ closure (globalBumpV₁ (I := I) (M := M) α) ↔
        globalBumpψ (I := I) (M := M) α x = 1) ∧
      (∀ x, x ∈ (globalBumpV₂ (I := I) (M := M) α)ᶜ ↔
        globalBumpψ (I := I) (M := M) α x = 0) := by
  classical
  unfold globalBumpV₁ globalBumpV₂ globalBumpψ
  exact Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec (exists_globalBump_data (I := I) (M := M) α)))

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma globalBumpV₁_isOpen (α : M) :
    IsOpen (globalBumpV₁ (I := I) (M := M) α) :=
  (globalBumpData_spec (I := I) (M := M) α).1

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pouTsupport_subset_globalBumpV₁ (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      globalBumpV₁ (I := I) (M := M) α :=
  (globalBumpData_spec (I := I) (M := M) α).2.2.1

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma closure_globalBumpV₁_subset_globalBumpV₂ (α : M) :
    closure (globalBumpV₁ (I := I) (M := M) α) ⊆
      globalBumpV₂ (I := I) (M := M) α :=
  (globalBumpData_spec (I := I) (M := M) α).2.2.2.1

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma closure_globalBumpV₂_subset_chartAt_source (α : M) :
    closure (globalBumpV₂ (I := I) (M := M) α) ⊆ (chartAt H α).source :=
  (globalBumpData_spec (I := I) (M := M) α).2.2.2.2.1

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma globalBumpψ_contMDiff (α : M) :
    ContMDiff I 𝓘(ℝ) ∞ (globalBumpψ (I := I) (M := M) α) :=
  (globalBumpData_spec (I := I) (M := M) α).2.2.2.2.2.1

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma globalBumpψ_eq_one_on_closure_V₁ (α : M) {b : M}
    (hb : b ∈ closure (globalBumpV₁ (I := I) (M := M) α)) :
    globalBumpψ (I := I) (M := M) α b = 1 :=
  ((globalBumpData_spec (I := I) (M := M) α).2.2.2.2.2.2.2.1 b).mp hb

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma globalBumpψ_eq_zero_off_V₂ (α : M) {b : M}
    (hb : b ∈ (globalBumpV₂ (I := I) (M := M) α)ᶜ) :
    globalBumpψ (I := I) (M := M) α b = 0 :=
  ((globalBumpData_spec (I := I) (M := M) α).2.2.2.2.2.2.2.2 b).mp hb

noncomputable def chartFrameNormGlobalSmooth
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := by
  classical
  set u : Set M := (chartAt H α).source with hu_def
  have hu_open : IsOpen u := (chartAt H α).open_source
  have hψ_tsupport_subset_clV₂ :
      tsupport (globalBumpψ (I := I) (M := M) α) ⊆
        closure (globalBumpV₂ (I := I) (M := M) α) := by
    have h_supp : Function.support (globalBumpψ (I := I) (M := M) α) ⊆
        globalBumpV₂ (I := I) (M := M) α := by
      intro x hx
      by_contra hxV₂
      have hx_in : x ∈ (globalBumpV₂ (I := I) (M := M) α)ᶜ := hxV₂
      have hψx : globalBumpψ (I := I) (M := M) α x = 0 :=
        globalBumpψ_eq_zero_off_V₂ (I := I) (M := M) α hx_in
      exact hx hψx
    exact closure_mono h_supp
  have hψ_tsupport_subset_u :
      tsupport (globalBumpψ (I := I) (M := M) α) ⊆ u :=
    hψ_tsupport_subset_clV₂.trans
      (closure_globalBumpV₂_subset_chartAt_source (I := I) (M := M) α)
  have hψ_smoothOn : ContMDiffOn I 𝓘(ℝ) ∞ (globalBumpψ (I := I) (M := M) α) u :=
    (globalBumpψ_contMDiff (I := I) (M := M) α).contMDiffOn
  have hs_smoothOn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => chartFrameNorm (I := I) g α i b)) u := by
    rw [show u = (trivializationAt E (TangentSpace I) α).baseSet from rfl]
    exact chartFrameNorm_contMDiffOn (I := I) g α i
  have h := ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (n := ∞)
    (V := TangentSpace I) hψ_smoothOn hu_open hψ_tsupport_subset_u hs_smoothOn
  refine ⟨fun b : M =>
    globalBumpψ (I := I) (M := M) α b • chartFrameNorm (I := I) g α i b, ?_⟩
  exact h

omit [I.Boundaryless] in
private lemma chartFrameNormGlobalSmooth_toFun_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (b : M) :
    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b =
      globalBumpψ (I := I) (M := M) α b • chartFrameNorm (I := I) g α i b := by
  classical
  unfold chartFrameNormGlobalSmooth
  rfl

omit [I.Boundaryless] in
theorem chartFrameNormGlobalSmooth_eq_chartFrameNorm_on_pouTsupportNbhd
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∃ U : Set M, IsOpen U ∧
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆ U ∧
      U ⊆ (chartAt H α).source ∧
      ∀ b ∈ U, (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b =
        chartFrameNorm (I := I) g α i b := by
  classical
  refine ⟨globalBumpV₁ (I := I) (M := M) α, ?_, ?_, ?_, ?_⟩
  · exact globalBumpV₁_isOpen (I := I) (M := M) α
  · exact pouTsupport_subset_globalBumpV₁ (I := I) (M := M) α
  · intro b hb
    have h₁ : b ∈ closure (globalBumpV₁ (I := I) (M := M) α) := subset_closure hb
    have h₂ : b ∈ globalBumpV₂ (I := I) (M := M) α :=
      closure_globalBumpV₁_subset_globalBumpV₂ (I := I) (M := M) α h₁
    have h₃ : b ∈ closure (globalBumpV₂ (I := I) (M := M) α) := subset_closure h₂
    exact closure_globalBumpV₂_subset_chartAt_source (I := I) (M := M) α h₃
  · intro b hb
    have hψ : globalBumpψ (I := I) (M := M) α b = 1 :=
      globalBumpψ_eq_one_on_closure_V₁ (I := I) (M := M) α (subset_closure hb)
    rw [chartFrameNormGlobalSmooth_toFun_apply, hψ, one_smul]

omit [I.Boundaryless] in
theorem chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M}
    (hb : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α j).toFun b) =
      if i = j then 1 else 0 := by
  classical
  obtain ⟨U_i, _hU_i_open, htsupp_U_i, hU_i_source, hU_eq_i⟩ :=
    chartFrameNormGlobalSmooth_eq_chartFrameNorm_on_pouTsupportNbhd
      (I := I) (M := M) g α i
  obtain ⟨U_j, _hU_j_open, htsupp_U_j, _hU_j_source, hU_eq_j⟩ :=
    chartFrameNormGlobalSmooth_eq_chartFrameNorm_on_pouTsupportNbhd
      (I := I) (M := M) g α j
  have hb_pou : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := hb.1
  have hb_U_i : b ∈ U_i := htsupp_U_i hb_pou
  have hb_U_j : b ∈ U_j := htsupp_U_j hb_pou
  have hb_source : b ∈ (chartAt H α).source := hU_i_source hb_U_i
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hb_source
  have h_eq_i : (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b =
      chartFrameNorm (I := I) g α i b := hU_eq_i b hb_U_i
  have h_eq_j : (chartFrameNormGlobalSmooth (I := I) (M := M) g α j).toFun b =
      chartFrameNorm (I := I) g α j b := hU_eq_j b hb_U_j
  rw [h_eq_i, h_eq_j]
  exact chartFrameNorm_orthonormal (I := I) g α hb_base i j

end Connection
end Integral
end DifferentialGeometry
