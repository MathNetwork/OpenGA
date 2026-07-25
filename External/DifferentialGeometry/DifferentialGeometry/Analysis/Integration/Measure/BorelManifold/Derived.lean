import DifferentialGeometry.Analysis.Integration.Measure.BorelManifold.Defs
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Hom
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Set MeasureTheory Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Measure
namespace BorelManifold

open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem measurable_of_continuousOn_chart_source
    [IsBorelChartedSpace H M] [Nonempty M]
    {F : Type*} [TopologicalSpace F]
    (f : M → F) (hf : ∀ α : M, ContinuousOn f (chartAt H α).source) :
    @Measurable M F (borel M) (borel F) f := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  classical
  have hcount := IsBorelChartedSpace.chartAt_range_countable (H := H) (M := M)
  have hmeas := IsBorelChartedSpace.measurableSet_chartAt_preimage (H := H) (M := M)
  have hrange_nonempty : (Set.range (fun x : M => chartAt H x)).Nonempty :=
    Set.range_nonempty (fun x : M => chartAt H x)
  obtain ⟨φ, hφ⟩ := hcount.exists_eq_range hrange_nonempty
  set s : ℕ → Set M := fun n => {x : M | chartAt H x = φ n} with hs_def
  have hsmeas : ∀ n, MeasurableSet (s n) := fun n => hmeas (φ n)
  have hssub : ∀ n, s n ⊆ (φ n).source := by
    intro n x hx
    have hxs : x ∈ (chartAt H x).source := ChartedSpace.mem_chart_source x
    have hxe : chartAt H x = φ n := hx
    rw [hxe] at hxs
    exact hxs
  have hcov : (⋃ n, s n) = univ := by
    refine Set.eq_univ_of_forall (fun x => ?_)
    have hxr : chartAt H x ∈ Set.range (fun y : M => chartAt H y) :=
      Set.mem_range_self x
    rw [hφ] at hxr
    obtain ⟨n, hn⟩ := hxr
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change chartAt H x = φ n
    exact hn.symm
  have hsne : ∀ n, (s n).Nonempty := by
    intro n
    have hin : φ n ∈ Set.range (fun y : M => chartAt H y) := by
      rw [hφ]; exact Set.mem_range_self n
    obtain ⟨x, hx⟩ := hin
    exact ⟨x, hx⟩
  have hf_φ : ∀ n, ContinuousOn f (φ n).source := by
    intro n
    obtain ⟨x₀, hx₀⟩ := hsne n
    have hh : chartAt H x₀ = φ n := hx₀
    have hcx := hf x₀
    rw [hh] at hcx
    exact hcx
  have hopen_source : ∀ n, IsOpen (φ n).source := fun n => (φ n).open_source
  refine measurable_of_isOpen ?_
  intro U hU
  have hpre : f ⁻¹' U = ⋃ n, f ⁻¹' U ∩ s n := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      have hxc : x ∈ ⋃ n, s n := by rw [hcov]; exact mem_univ x
      obtain ⟨n, hn⟩ := mem_iUnion.mp hxc
      exact ⟨n, hx, hn⟩
    · rintro ⟨n, hx, _⟩
      exact hx
  rw [hpre]
  refine MeasurableSet.iUnion (fun n => ?_)
  have h1 : f ⁻¹' U ∩ s n = ((φ n).source ∩ f ⁻¹' U) ∩ s n := by
    ext y
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hyU, hys⟩
      exact ⟨⟨hssub n hys, hyU⟩, hys⟩
    · rintro ⟨⟨_, hyU⟩, hys⟩
      exact ⟨hyU, hys⟩
  rw [h1]
  have hopen : IsOpen ((φ n).source ∩ f ⁻¹' U) :=
    (hf_φ n).isOpen_inter_preimage (hopen_source n) hU
  exact MeasurableSet.inter hopen.measurableSet (hsmeas n)

private lemma rs_baseSet_eq_chart_source' (α : M) (r s : ℕ) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α).baseSet =
      (chartAt H α).source := by
  change ((trivializationAt (Tensor0SModel r ℝ E)
              (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel s ℝ E)
              (fun x : M => Tensor0SSpace s I x) α).baseSet) =
        (chartAt H α).source
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
  rw [Set.inter_self]
  rfl

private lemma contMDiffOn_trivProj
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (α : M) :
    ContMDiffOn I (𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α
          ⟨x, S.toSection x⟩).2)
      ((chartAt H α).source) := by
  letI : IsManifold I (∞ + 1) M := by
    have : ((∞ : WithTop ℕ∞) + 1) = ∞ := by
      simp
    rw [this]; infer_instance
  letI : ContMDiffVectorBundle ∞ (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) I :=
    tensorRSBundle_smooth (n := ∞) r s
  have hbase := rs_baseSet_eq_chart_source' (I := I) (M := M) α r s
  have hsmooth_total :
      ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E) x (S.toSection x)) :=
    S.toSection.contMDiff
  have hrewrite := (Bundle.Trivialization.contMDiffOn_section_baseSet_iff
    (e := trivializationAt (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) α)).mp hsmooth_total.contMDiffOn
  rw [hbase] at hrewrite
  exact hrewrite

private lemma continuousOn_trivProj
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (α : M) :
    ContinuousOn
      (fun x : M => (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α
          ⟨x, S.toSection x⟩).2)
      ((chartAt H α).source) :=
  (contMDiffOn_trivProj (I := I) (M := M) S α).continuousOn

omit [Module.Finite ℝ E] in
private lemma tangent_continuousLinearMapAt_levelSet (α x : M)
    (hx : chartAt H x = chartAt H α) :
    (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x =
      (1 : E →L[ℝ] E) := by
  have hx_src : x ∈ (chartAt H α).source := by
    have hxs : x ∈ (chartAt H x).source := ChartedSpace.mem_chart_source x
    rw [hx] at hxs
    exact hxs
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (b₀ := α) (b := x) hx_src]
  have hach : achart H x = achart H α := by
    apply Subtype.ext
    change chartAt H x = chartAt H α
    exact hx
  ext v
  rw [hach]
  exact (tangentBundleCore I M).coordChange_self (achart H α) x
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact hx_src) v

omit [Module.Finite ℝ E] in
private lemma tangent_symmL_levelSet (α x : M)
    (hx : chartAt H x = chartAt H α) :
    (trivializationAt E (TangentSpace I) α).symmL ℝ x = (1 : E →L[ℝ] E) := by
  have hx_src : x ∈ (chartAt H α).source := by
    have hxs : x ∈ (chartAt H x).source := ChartedSpace.mem_chart_source x
    rw [hx] at hxs
    exact hxs
  rw [TangentBundle.symmL_trivializationAt_eq_core
    (b₀ := α) (b := x) hx_src]
  have hach : achart H x = achart H α := by
    apply Subtype.ext
    change chartAt H x = chartAt H α
    exact hx
  ext v
  rw [hach]
  exact (tangentBundleCore I M).coordChange_self (achart H α) x
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact hx_src) v

private lemma tensor0S_continuousLinearMapAt_levelSet_apply
    (s : ℕ) (α x : M) (hx : chartAt H x = chartAt H α)
    (p : Tensor0SSpace s I x) :
    (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ x p = p := by
  have hx_src : x ∈ (chartAt H α).source := by
    have hxs : x ∈ (chartAt H x).source := ChartedSpace.mem_chart_source x
    rw [hx] at hxs
    exact hxs
  have hx_base : x ∈ (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).baseSet := by
    change x ∈ (trivializationAt E (TangentSpace I) α).baseSet
    change x ∈ (chartAt H α).source
    exact hx_src
  have hcLMAt :
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ x p =
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α ⟨x, p⟩).2 := by
    change (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).linearMapAt ℝ x p = _
    rw [Bundle.Trivialization.linearMapAt_apply, if_pos hx_base]
  rw [hcLMAt]
  have happly : (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α ⟨x, p⟩).2 =
      p.compContinuousLinearMap
        (fun _ => (trivializationAt E (TangentSpace I) α).symmL ℝ x) := rfl
  rw [happly, tangent_symmL_levelSet (I := I) (M := M) α x hx]
  ext v
  change p (fun i => (1 : E →L[ℝ] E) (v i)) = p v
  congr

private lemma tensor0S_symmL_levelSet_apply
    (s : ℕ) (α x : M) (hx : chartAt H x = chartAt H α)
    (p : Tensor0SModel s ℝ E) :
    (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).symmL ℝ x p = p := by
  have hx_src : x ∈ (chartAt H α).source := by
    have hxs : x ∈ (chartAt H x).source := ChartedSpace.mem_chart_source x
    rw [hx] at hxs
    exact hxs
  have hx_base : x ∈ (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).baseSet := by
    change x ∈ (trivializationAt E (TangentSpace I) α).baseSet
    change x ∈ (chartAt H α).source
    exact hx_src
  have hinv : (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ x
      ((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).symmL ℝ x p) = p :=
    Bundle.Trivialization.continuousLinearMapAt_symmL
      (R := ℝ) (e := trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α) hx_base p
  have hid := tensor0S_continuousLinearMapAt_levelSet_apply (I := I) (M := M) s α x hx
    ((trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).symmL ℝ x p)
  exact hid.symm.trans hinv

private lemma tensorRS_levelSet_identity
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) (α x : M)
    (hx : chartAt H x = chartAt H α) :
    (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α ⟨x, S.toSection x⟩).2 = S.toFun x := by
  have heq :
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α ⟨x, S.toSection x⟩).2 =
      ContinuousLinearMap.inCoordinates (Tensor0SModel r ℝ E) (Tensor0SSpace r I)
        (Tensor0SModel s ℝ E) (Tensor0SSpace s I) α x α x (S.toSection x) := by
    rfl
  rw [heq]
  ext v
  unfold ContinuousLinearMap.inCoordinates
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [tensor0S_symmL_levelSet_apply (I := I) (M := M) r α x hx v]
  rw [tensor0S_continuousLinearMapAt_levelSet_apply (I := I) (M := M) s α x hx
    ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from S.toSection x) v)]
  rfl

theorem SmoothCcTensor.measurable_toFun
    [IsBorelChartedSpace H M] [Nonempty M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    @Measurable M (TensorRSModel r s ℝ E) (borel M) _ S.toFun := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace (TensorRSModel r s ℝ E) := borel (TensorRSModel r s ℝ E)
  haveI : BorelSpace (TensorRSModel r s ℝ E) := ⟨rfl⟩
  classical
  have hcount := IsBorelChartedSpace.chartAt_range_countable (H := H) (M := M)
  have hmeas_lvl := IsBorelChartedSpace.measurableSet_chartAt_preimage (H := H) (M := M)
  have hrange_nonempty : (Set.range (fun y : M => chartAt H y)).Nonempty :=
    Set.range_nonempty (fun y : M => chartAt H y)
  obtain ⟨φ, hφ⟩ := hcount.exists_eq_range hrange_nonempty
  set s' : ℕ → Set M := fun n => {x : M | chartAt H x = φ n} with hs'_def
  have hs'meas : ∀ n, MeasurableSet (s' n) := fun n => hmeas_lvl (φ n)
  have hs'sub : ∀ n, s' n ⊆ (φ n).source := by
    intro n x hx
    have hxs : x ∈ (chartAt H x).source := ChartedSpace.mem_chart_source x
    have hxe : chartAt H x = φ n := hx
    rw [hxe] at hxs
    exact hxs
  have hs'ne : ∀ n, (s' n).Nonempty := by
    intro n
    have hin : φ n ∈ Set.range (fun y : M => chartAt H y) := by
      rw [hφ]; exact Set.mem_range_self n
    obtain ⟨x, hx⟩ := hin
    exact ⟨x, hx⟩
  choose xn hxn using hs'ne
  have hcov : (⋃ n, s' n) = univ := by
    refine Set.eq_univ_of_forall (fun x => ?_)
    have hxr : chartAt H x ∈ Set.range (fun y : M => chartAt H y) :=
      Set.mem_range_self x
    rw [hφ] at hxr
    obtain ⟨n, hn⟩ := hxr
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change chartAt H x = φ n
    exact hn.symm
  set g_n : ℕ → M → TensorRSModel r s ℝ E := fun n x =>
      (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) (xn n) ⟨x, S.toSection x⟩).2
    with hg_n_def
  have hg_n_cont : ∀ n, ContinuousOn (g_n n) (chartAt H (xn n)).source := by
    intro n
    exact continuousOn_trivProj (I := I) (M := M) S (xn n)
  have hg_n_eq : ∀ n, ∀ x ∈ s' n, g_n n x = S.toFun x := by
    intro n x hx
    have hxφ : chartAt H x = φ n := hx
    have hxnφ : chartAt H (xn n) = φ n := hxn n
    have hx_eq : chartAt H x = chartAt H (xn n) := by rw [hxφ, hxnφ]
    exact tensorRS_levelSet_identity (I := I) (M := M) S (xn n) x hx_eq
  have hs'sub_chartXn : ∀ n, s' n ⊆ (chartAt H (xn n)).source := by
    intro n x hx
    have h1 : x ∈ (φ n).source := hs'sub n hx
    have hxnφ : chartAt H (xn n) = φ n := hxn n
    rw [hxnφ]
    exact h1
  refine measurable_of_isOpen ?_
  intro U hU
  have hpre : S.toFun ⁻¹' U = ⋃ n, S.toFun ⁻¹' U ∩ s' n := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      have hxc : x ∈ ⋃ n, s' n := by rw [hcov]; exact mem_univ x
      obtain ⟨n, hn⟩ := mem_iUnion.mp hxc
      exact ⟨n, hx, hn⟩
    · rintro ⟨n, hx, _⟩
      exact hx
  rw [hpre]
  refine MeasurableSet.iUnion (fun n => ?_)
  have heq_pre : S.toFun ⁻¹' U ∩ s' n = (g_n n) ⁻¹' U ∩ s' n := by
    ext x
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hxU, hxs⟩
      have h := hg_n_eq n x hxs
      rw [h]
      exact ⟨hxU, hxs⟩
    · rintro ⟨hxU, hxs⟩
      have h := hg_n_eq n x hxs
      rw [h] at hxU
      exact ⟨hxU, hxs⟩
  rw [heq_pre]
  have h1 : (g_n n) ⁻¹' U ∩ s' n =
      ((chartAt H (xn n)).source ∩ ((g_n n) ⁻¹' U)) ∩ s' n := by
    ext y
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hyU, hys⟩
      exact ⟨⟨hs'sub_chartXn n hys, hyU⟩, hys⟩
    · rintro ⟨⟨_, hyU⟩, hys⟩
      exact ⟨hyU, hys⟩
  rw [h1]
  have hopen : IsOpen ((chartAt H (xn n)).source ∩ (g_n n) ⁻¹' U) :=
    (hg_n_cont n).isOpen_inter_preimage (chartAt H (xn n)).open_source hU
  exact MeasurableSet.inter hopen.measurableSet (hs'meas n)

theorem SmoothCcTensor.stronglyMeasurable_toFun
    [IsBorelChartedSpace H M] [Nonempty M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s) :
    @StronglyMeasurable M (TensorRSModel r s ℝ E) _ (borel M) S.toFun := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  letI : MeasurableSpace (TensorRSModel r s ℝ E) := borel (TensorRSModel r s ℝ E)
  haveI : BorelSpace (TensorRSModel r s ℝ E) := ⟨rfl⟩
  have hmeas := SmoothCcTensor.measurable_toFun (I := I) (M := M) S
  exact hmeas.stronglyMeasurable

theorem SmoothCcTensor.aestronglyMeasurable_toFun
    [IsBorelChartedSpace H M] [Nonempty M]
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (S : SmoothCcTensor g r s)
    (μ : letI : MeasurableSpace M := borel M; MeasureTheory.Measure M) :
    letI : MeasurableSpace M := borel M
    AEStronglyMeasurable S.toFun μ := by
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  exact (SmoothCcTensor.stronglyMeasurable_toFun (I := I) (M := M) S).aestronglyMeasurable

end BorelManifold

end Measure
end Integral
end DifferentialGeometry

end
