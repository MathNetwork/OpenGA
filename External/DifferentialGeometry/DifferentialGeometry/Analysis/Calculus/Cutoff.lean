import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false









namespace DifferentialGeometry.Analysis

open Filter Set
open scoped ContDiff Manifold Topology



theorem contDiff_cutoff_smul
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U)
    {χ : E → ℝ} {f : E → F}
    (hχ : ContDiff ℝ ∞ χ)
    (hχU : tsupport χ ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (fun x => χ x • f x) := by
  rw [← contDiffOn_univ]
  intro x _
  by_cases hx : x ∈ tsupport χ
  · have hxU : x ∈ U := hχU hx
    exact hχ.contDiffAt.contDiffWithinAt.smul
      ((hf.contDiffAt (hU.mem_nhds hxU)).contDiffWithinAt)
  · have hopen : (tsupport χ)ᶜ ∈ 𝓝 x :=
      (isClosed_tsupport χ).isOpen_compl.mem_nhds hx
    have heq : (fun y => χ y • f y) =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
      filter_upwards [hopen] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt




theorem exists_bump_one_on
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E}
    (hK : IsCompact K)
    (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : E → ℝ,
      ContDiff ℝ ∞ χ ∧
      Set.EqOn χ 1 K ∧
      tsupport χ ⊆ U ∧
      Set.range χ ⊆ Set.Icc 0 1 := by
  haveI : NormalSpace E := inferInstance
  haveI : LocallyCompactSpace E := inferInstance
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χM, hχone, hχzero, hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓘(ℝ, E)) (M := E) (n := (⊤ : ℕ∞)) hK.isClosed hKL
  let χ : E → ℝ := χM
  refine ⟨χ, ?_, ?_, ?_, Set.range_subset_iff.mpr hχrange⟩
  · exact contMDiff_iff_contDiff.mp
      (χM.contMDiff.of_le (by exact_mod_cast le_top))
  · intro x hx
    exact hχone.self_of_nhdsSet x hx
  · change closure (Function.support χ) ⊆ U
    exact (closure_minimal
      (fun x hx => by
        by_contra hxL
        exact hx (hχzero x hxL))
      hL.isClosed).trans hLU

end DifferentialGeometry.Analysis
