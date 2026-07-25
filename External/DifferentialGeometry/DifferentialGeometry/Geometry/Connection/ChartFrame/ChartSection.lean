import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity


noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

def chartE_section_repr (α : M) (σ : Π x : M, TangentSpace I x) (x : M) : E :=
  (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x (σ x)

omit [FiniteDimensional ℝ E] in
lemma chartE_section_repr_def (α : M) (σ : Π x : M, TangentSpace I x) :
    chartE_section_repr (I := I) α σ =
      fun x : M =>
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x (σ x) :=
  rfl

omit [FiniteDimensional ℝ E] in
lemma chartE_section_repr_apply
    (α : M) (σ : Π x : M, TangentSpace I x) (x : M) :
    chartE_section_repr (I := I) α σ x =
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x (σ x) := rfl

omit [FiniteDimensional ℝ E] in
lemma chartE_section_repr_eq_trivialization_snd
    (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartE_section_repr (I := I) α σ x =
      (trivializationAt E (TangentSpace I) α ⟨x, σ x⟩).2 := by
  classical
  unfold chartE_section_repr
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    trivializationAt E (TangentSpace I) α
  rw [T.apply_eq_prod_continuousLinearEquivAt ℝ x hx (σ x)]
  rw [show (x, (T.continuousLinearEquivAt ℝ x hx) (σ x)).2 =
        T.continuousLinearEquivAt ℝ x hx (σ x) from rfl]
  rw [show (T.continuousLinearEquivAt ℝ x hx (σ x) : E) =
          T.continuousLinearMapAt ℝ x (σ x) from
        congrFun (T.coe_continuousLinearEquivAt_eq (R := ℝ) hx) (σ x)]

variable (I) in

omit [FiniteDimensional ℝ E] in
theorem mdifferentiableWithinAt_section_iff_chartE
    (α : M) (σ : Π x : M, TangentSpace I x) {u : Set M} {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    MDiffAt[u] (T% σ) x ↔ MDiffAt[u] (chartE_section_repr (I := I) α σ) x := by
  classical
  have hiff :=
    Bundle.Trivialization.mdifferentiableWithinAt_section_iff (𝕜 := ℝ) I (u := u)
      (e := trivializationAt E (TangentSpace I) α) σ hx
  refine hiff.trans ?_
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine h.congr_of_eventuallyEq (f₁ := chartE_section_repr (I := I) α σ) ?_ ?_
    · filter_upwards
        [mem_nhdsWithin_of_mem_nhds
          ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx)] with y hy
      exact chartE_section_repr_eq_trivialization_snd (I := I) α σ hy
    · exact chartE_section_repr_eq_trivialization_snd (I := I) α σ hx
  · refine h.congr_of_eventuallyEq
        (f₁ := fun y => (trivializationAt E (TangentSpace I) α ⟨y, σ y⟩).2) ?_ ?_
    · filter_upwards
        [mem_nhdsWithin_of_mem_nhds
          ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx)] with y hy
      exact (chartE_section_repr_eq_trivialization_snd (I := I) α σ hy).symm
    · exact (chartE_section_repr_eq_trivialization_snd (I := I) α σ hx).symm

variable (I) in

omit [FiniteDimensional ℝ E] in
theorem mdifferentiableAt_section_iff_chartE
    (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    MDiffAt (T% σ) x ↔ MDiffAt (chartE_section_repr (I := I) α σ) x := by
  classical
  rw [← mdifferentiableWithinAt_univ, ← mdifferentiableWithinAt_univ]
  exact mdifferentiableWithinAt_section_iff_chartE I α σ hx

omit [FiniteDimensional ℝ E] in
private lemma mdifferentiableAt_iff_pullback_of_mem_source
    (α : M) (f : M → E) {x : M} (hx : x ∈ (chartAt H α).source) :
    MDiffAt f x ↔
      MDiffAt[range I] (f ∘ (extChartAt I α).symm) (extChartAt I α x) :=
  mdifferentiableAt_iff_source_of_mem_source (x := α) (x' := x) hx

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private lemma mdifferentiableWithinAt_range_iff_differentiableAt_of_interior
    {α : M} {f : E → E} {y : E}
    (hy_int : y ∈ interior ((extChartAt I α).target : Set E)) :
    MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E) f (range I) y ↔ DifferentiableAt ℝ f y := by
  classical
  have htgt : (extChartAt I α).target ⊆ range I := extChartAt_target_subset_range α
  have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) := isOpen_interior
  have hrange_nhds : range I ∈ 𝓝 y :=
    Filter.mem_of_superset (hint_open.mem_nhds hy_int)
      (interior_subset.trans htgt)
  rw [mdifferentiableWithinAt_iff_differentiableWithinAt]
  exact ⟨fun h => h.differentiableAt hrange_nhds, fun h => h.differentiableWithinAt⟩

variable (I) in

omit [FiniteDimensional ℝ E] in
theorem mdifferentiableAt_section_iff_chartE_fderiv
    (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx_src : x ∈ (chartAt H α).source)
    (hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E)) :
    MDiffAt (T% σ) x ↔
      DifferentiableAt ℝ
        (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
        (extChartAt I α x) := by
  classical
  rw [mdifferentiableAt_section_iff_chartE I α σ hx_base]
  rw [mdifferentiableAt_iff_pullback_of_mem_source α
      (chartE_section_repr (I := I) α σ) hx_src]
  exact mdifferentiableWithinAt_range_iff_differentiableAt_of_interior (α := α) hx_int

variable (I) in

omit [FiniteDimensional ℝ E] in
theorem contMDiffWithinAt_section_iff_chartE
    {k : ℕ∞} (α : M) (σ : Π x : M, TangentSpace I x) {u : Set M} {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) k (T% σ) u x ↔
      ContMDiffWithinAt I 𝓘(ℝ, E) k (chartE_section_repr (I := I) α σ) u x := by
  classical
  have hiff :=
    Bundle.Trivialization.contMDiffWithinAt_section (𝕜 := ℝ) (IB := I)
      (n := (k : WithTop ℕ∞)) (s := σ) (a := u)
      (e := trivializationAt E (TangentSpace I) α) hx
  refine hiff.trans ?_
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine h.congr_of_eventuallyEq (f₁ := chartE_section_repr (I := I) α σ) ?_ ?_
    · filter_upwards
        [mem_nhdsWithin_of_mem_nhds
          ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx)] with y hy
      exact (chartE_section_repr_eq_trivialization_snd (I := I) α σ hy)
    · exact chartE_section_repr_eq_trivialization_snd (I := I) α σ hx
  · refine h.congr_of_eventuallyEq
        (f₁ := fun y => (trivializationAt E (TangentSpace I) α ⟨y, σ y⟩).2) ?_ ?_
    · filter_upwards
        [mem_nhdsWithin_of_mem_nhds
          ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hx)] with y hy
      exact (chartE_section_repr_eq_trivialization_snd (I := I) α σ hy).symm
    · exact (chartE_section_repr_eq_trivialization_snd (I := I) α σ hx).symm

variable (I) in

omit [FiniteDimensional ℝ E] in
theorem contMDiffAt_section_iff_chartE
    {k : ℕ∞} (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) k (T% σ) x ↔
      ContMDiffAt I 𝓘(ℝ, E) k (chartE_section_repr (I := I) α σ) x := by
  classical
  rw [← contMDiffWithinAt_univ, ← contMDiffWithinAt_univ]
  exact contMDiffWithinAt_section_iff_chartE I α σ hx

variable (I) in

omit [FiniteDimensional ℝ E] in
theorem mfderiv_section_eq_chartE_fderiv
    (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx_src : x ∈ (chartAt H α).source)
    (hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E))
    (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ, E) (chartE_section_repr (I := I) α σ) x) v =
      fderiv ℝ (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
        (extChartAt I α x)
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v) := by
  classical
  set fE := chartE_section_repr (I := I) α σ
  set φ := extChartAt I α
  set y₀ : E := φ x
  set gE : E → E := fE ∘ φ.symm
  have hfE_eqOn : ∀ y, y ∈ φ.source → fE y = gE (φ y) := by
    intro y hy
    change fE y = fE (φ.symm (φ y))
    have : φ.symm (φ y) = y := φ.left_inv hy
    rw [this]
  have hsrc_extChart : x ∈ φ.source := by
    rw [extChartAt_source]; exact hx_src
  have hsrc_nhds : φ.source ∈ 𝓝 x := extChartAt_source_mem_nhds' (I := I) hsrc_extChart
  have hev : fE =ᶠ[𝓝 x] gE ∘ φ := by
    filter_upwards [hsrc_nhds] with y hy
    exact hfE_eqOn y hy
  have hmfderiv_eq :
      mfderiv I 𝓘(ℝ, E) fE x = mfderiv I 𝓘(ℝ, E) (gE ∘ φ) x :=
    Filter.EventuallyEq.mfderiv_eq hev
  have hφ_mdiff : MDiffAt φ x := mdifferentiableAt_extChartAt (I := I) (x := α) hx_src
  have hgE_diff : DifferentiableAt ℝ gE y₀ :=
    (mdifferentiableAt_section_iff_chartE_fderiv (I := I) α σ hx_src hx_base hx_int).mp hσ
  have hgE_mdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) gE y₀ :=
    hgE_diff.mdifferentiableAt
  have hchain :
      mfderiv I 𝓘(ℝ, E) (gE ∘ φ) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) gE (φ x)).comp (mfderiv I 𝓘(ℝ, E) φ x) :=
    mfderiv_comp x hgE_mdiff hφ_mdiff
  have hmf_to_fderiv :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) gE (φ x) = fderiv ℝ gE (φ x) :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (E := E) (E' := E) (f := gE) (x := φ x)
  have htriv_eq :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x =
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x :=
    (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx_src).symm
  rw [hmfderiv_eq, hchain, hmf_to_fderiv]
  change (fderiv ℝ gE (φ x))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) v) =
      fderiv ℝ gE y₀
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v)
  rw [htriv_eq]
  rfl

variable (I) in

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_chartE_pullback_of_contMDiff_section
    {k : ℕ∞} (α : M) (σ : Π x : M, TangentSpace I x)
    (hσ : ContMDiff I (I.prod 𝓘(ℝ, E)) k (T% σ)) :
    ContDiffOn ℝ k
      (chartE_section_repr (I := I) α σ ∘ (extChartAt I α).symm)
      ((extChartAt I α) ''
        ((chartAt H α).source ∩ (trivializationAt E (TangentSpace I) α).baseSet) ∩
        (extChartAt I α).target) := by
  classical
  intro y hy
  obtain ⟨⟨x, ⟨hx_src, hx_base⟩, hx_eq⟩, hy_target⟩ := hy
  subst hx_eq
  set fE := chartE_section_repr (I := I) α σ
  set φ := extChartAt I α
  have hfE_at : ContMDiffAt I 𝓘(ℝ, E) k fE x :=
    (contMDiffAt_section_iff_chartE I α σ hx_base).mp (hσ x)
  have hxφ_src : x ∈ φ.source := by rw [extChartAt_source]; exact hx_src
  have hxφ_tgt : φ x ∈ φ.target := φ.map_source hxφ_src
  have hxφ_inv : φ.symm (φ x) = x := φ.left_inv hxφ_src
  have hsymm_at : ContMDiffWithinAt 𝓘(ℝ, E) I (k : WithTop ℕ∞) φ.symm φ.target (φ x) := by
    have hsymm_on_inf : ContMDiffOn 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) φ.symm φ.target :=
      contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
    have hsymm_on : ContMDiffOn 𝓘(ℝ, E) I (k : WithTop ℕ∞) φ.symm φ.target :=
      hsymm_on_inf.of_le (by exact_mod_cast le_top)
    exact hsymm_on (φ x) hxφ_tgt
  have hcomp_at : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E) k (fE ∘ φ.symm) φ.target (φ x) := by
    have hfE_at' : ContMDiffAt I 𝓘(ℝ, E) k fE (φ.symm (φ x)) := by
      rw [hxφ_inv]; exact hfE_at
    exact hfE_at'.comp_contMDiffWithinAt (φ x) hsymm_at
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hcomp_at
  refine hcomp_at.mono ?_
  exact inter_subset_right

variable (I) in

abbrev trivToE (α x : M) : TangentSpace I x →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x

variable (I) in

abbrev trivFromE (α x : M) : E →L[ℝ] TangentSpace I x :=
  (trivializationAt E (TangentSpace I) α).symmL ℝ x

variable (I) in

omit [FiniteDimensional ℝ E] in
@[simp] lemma trivFromE_trivToE
    (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v : TangentSpace I x) :
    trivFromE (I := I) α x (trivToE (I := I) α x v) = v :=
  (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt (R := ℝ) hx v

variable (I) in

omit [FiniteDimensional ℝ E] in
@[simp] lemma trivToE_trivFromE
    (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (w : E) :
    trivToE (I := I) α x (trivFromE (I := I) α x w) = w :=
  (trivializationAt E (TangentSpace I) α).continuousLinearMapAt_symmL (R := ℝ) hx w

omit [FiniteDimensional ℝ E] in
@[simp] lemma chartE_section_repr_eq_trivToE
    (α : M) (σ : Π x : M, TangentSpace I x) (x : M) :
    chartE_section_repr (I := I) α σ x = trivToE (I := I) α x (σ x) := rfl

omit [FiniteDimensional ℝ E] in
lemma chartE_section_repr_add
    (α : M) (σ τ : Π x : M, TangentSpace I x) (x : M) :
    chartE_section_repr (I := I) α (σ + τ) x =
      chartE_section_repr (I := I) α σ x + chartE_section_repr (I := I) α τ x := by
  classical
  unfold chartE_section_repr
  rw [Pi.add_apply, map_add]

omit [FiniteDimensional ℝ E] in
lemma chartE_section_repr_smul
    (α : M) (c : ℝ) (σ : Π x : M, TangentSpace I x) (x : M) :
    chartE_section_repr (I := I) α (c • σ) x = c • chartE_section_repr (I := I) α σ x := by
  classical
  unfold chartE_section_repr
  rw [Pi.smul_apply, map_smul]

omit [FiniteDimensional ℝ E] in
lemma chartE_section_repr_smul_function
    (α : M) (f : M → ℝ) (σ : Π x : M, TangentSpace I x) (x : M) :
    chartE_section_repr (I := I) α (fun y => f y • σ y) x =
      f x • chartE_section_repr (I := I) α σ x := by
  classical
  unfold chartE_section_repr
  rw [map_smul]

omit [FiniteDimensional ℝ E] in
lemma chartE_section_repr_zero (α : M) (x : M) :
    chartE_section_repr (I := I) α (fun _ => (0 : TangentSpace I _)) x = 0 := by
  classical
  unfold chartE_section_repr
  rw [map_zero]

variable (I) in

omit [FiniteDimensional ℝ E] in
theorem mfderiv_scalar_eq_chart_fderiv
    (α : M) (f : M → ℝ) {x : M}
    (hx_src : x ∈ (chartAt H α).source)
    (hx_int : extChartAt I α x ∈ interior ((extChartAt I α).target : Set E))
    (hf : MDiffAt f x)
    (v : TangentSpace I x) :
    (mfderiv I 𝓘(ℝ) f x) v =
      fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)
        (trivToE (I := I) α x v) := by
  classical
  set φ := extChartAt I α
  set g : E → ℝ := f ∘ φ.symm
  have hf_eqOn : ∀ y, y ∈ φ.source → f y = g (φ y) := by
    intro y hy
    change f y = f (φ.symm (φ y))
    rw [φ.left_inv hy]
  have hsrc_extChart : x ∈ φ.source := by
    rw [extChartAt_source]; exact hx_src
  have hsrc_nhds : φ.source ∈ 𝓝 x := extChartAt_source_mem_nhds' (I := I) hsrc_extChart
  have hev : f =ᶠ[𝓝 x] g ∘ φ := by
    filter_upwards [hsrc_nhds] with y hy
    exact hf_eqOn y hy
  have hmfderiv_eq :
      mfderiv I 𝓘(ℝ) f x = mfderiv I 𝓘(ℝ) (g ∘ φ) x :=
    Filter.EventuallyEq.mfderiv_eq hev
  have hφ_mdiff : MDiffAt φ x := mdifferentiableAt_extChartAt (I := I) (x := α) hx_src
  have hxφ_tgt : φ x ∈ φ.target := φ.map_source hsrc_extChart
  have hxφ_inv : φ.symm (φ x) = x := φ.left_inv hsrc_extChart
  have hsymm_within :
      MDifferentiableWithinAt 𝓘(ℝ, E) I φ.symm (range I) (φ x) :=
    mdifferentiableWithinAt_extChartAt_symm (I := I) (x := α) hxφ_tgt
  have hrange_nhds : range I ∈ 𝓝 (φ x) := by
    have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) := isOpen_interior
    exact Filter.mem_of_superset
      (Filter.mem_of_superset (hint_open.mem_nhds hx_int) interior_subset)
      (extChartAt_target_subset_range α)
  have hg_within :
      MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ) g (range I) (φ x) :=
    MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq
      (I' := I) (I'' := 𝓘(ℝ)) (g := f) (f := φ.symm)
      (s := range I) (x := φ x) (y := x)
      hf hsymm_within hxφ_inv
  have hg_at : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) g (φ x) :=
    hg_within.mdifferentiableAt hrange_nhds
  have hchain :
      mfderiv I 𝓘(ℝ) (g ∘ φ) x =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g (φ x)).comp (mfderiv I 𝓘(ℝ, E) φ x) :=
    mfderiv_comp x hg_at hφ_mdiff
  have hg_diff : DifferentiableAt ℝ g (φ x) :=
    hg_at.differentiableAt
  have hmf_to_fderiv :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ) g (φ x) = fderiv ℝ g (φ x) :=
    mfderiv_eq_fderiv (𝕜 := ℝ) (E := E) (E' := ℝ) (f := g) (x := φ x)
  have htriv_eq :
      mfderiv I 𝓘(ℝ, E) (extChartAt I α) x =
        (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x :=
    (TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I)
      (x₀ := α) (x := x) hx_src).symm
  rw [hmfderiv_eq, hchain, hmf_to_fderiv]
  change (fderiv ℝ g (φ x))
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I α) x) v) =
      fderiv ℝ g (φ x)
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v)
  rw [htriv_eq]
  rfl

end Connection
end Integral
end DifferentialGeometry
