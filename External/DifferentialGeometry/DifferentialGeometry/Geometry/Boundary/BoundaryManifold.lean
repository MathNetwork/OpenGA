import DifferentialGeometry.Geometry.Boundary.ModelBoundary
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Compactness.SigmaCompact


noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private lemma infty_ne_zero_withTopENat : (∞ : WithTop ℕ∞) ≠ 0 := by
  intro h
  have h' : ((⊤ : ℕ∞) : WithTop ℕ∞) = ((0 : ℕ∞) : WithTop ℕ∞) := h
  exact ENat.top_ne_zero (WithTop.coe_eq_coe.mp h')

variable (I) (M) in

def BoundaryManifold : Type _ := {x : M // x ∈ I.boundary M}

instance : TopologicalSpace (BoundaryManifold I M) :=
  inferInstanceAs (TopologicalSpace {x : M // x ∈ I.boundary M})

instance : CoeOut (BoundaryManifold I M) M :=
  ⟨Subtype.val⟩

namespace BoundaryManifold

@[simp]
theorem coe_mk (x : M) (hx : x ∈ I.boundary M) :
    ((⟨x, hx⟩ : BoundaryManifold I M) : M) = x := rfl

theorem coe_injective :
    Function.Injective ((↑) : BoundaryManifold I M → M) :=
  Subtype.val_injective

@[ext]
theorem ext {x y : BoundaryManifold I M} (h : (x : M) = (y : M)) : x = y :=
  coe_injective h

theorem coe_mem (x : BoundaryManifold I M) : (x : M) ∈ I.boundary M := x.2

instance instT2Space [T2Space M] : T2Space (BoundaryManifold I M) :=
  inferInstanceAs (T2Space {x : M // x ∈ I.boundary M})

end BoundaryManifold

namespace BoundaryManifold

variable [hI : HasSmoothBoundary E H I]
variable [IsManifold I ∞ M]

def boundaryChartSource (x : BoundaryManifold I M) :
    Set (BoundaryManifold I M) :=
  {y : BoundaryManifold I M | (y : M) ∈ (chartAt H (x : M)).source}

def boundaryChartTarget (x : BoundaryManifold I M) :
    Set hI.boundaryH :=
  hI.inclH ⁻¹' (chartAt H (x : M)).target

omit hI [IsManifold I ∞ M] in
theorem isOpen_boundaryChartSource (x : BoundaryManifold I M) :
    IsOpen (boundaryChartSource (I := I) x) := by
  unfold boundaryChartSource
  exact (chartAt H (x : M)).open_source.preimage continuous_subtype_val

omit [IsManifold I ∞ M] in
theorem isOpen_boundaryChartTarget (x : BoundaryManifold I M) :
    IsOpen (boundaryChartTarget (I := I) x) := by
  unfold boundaryChartTarget
  exact (chartAt H (x : M)).open_target.preimage hI.inclH_continuous

def boundaryChartFun [Nonempty hI.boundaryH] (x y : BoundaryManifold I M) :
    hI.boundaryH :=
  Function.invFun hI.inclH (chartAt H (x : M) (y : M))

open Classical in

def boundaryChartInvFun (x : BoundaryManifold I M)
    (z : hI.boundaryH) : BoundaryManifold I M :=
  if h : (chartAt H (x : M)).symm (hI.inclH z) ∈ I.boundary M then
    ⟨(chartAt H (x : M)).symm (hI.inclH z), h⟩
  else
    x

omit hI in
theorem extChart_mem_frontier_of_mem_source
    {x y : BoundaryManifold I M}
    (hy : (y : M) ∈ (chartAt H (x : M)).source) :
    I (chartAt H (x : M) (y : M)) ∈ frontier (Set.range I) := by
  have hyx : I.IsBoundaryPoint (y : M) := y.2
  have hOne : (∞ : WithTop ℕ∞) ≠ 0 := infty_ne_zero_withTopENat
  have hAtlas : chartAt H (x : M) ∈ atlas H M := chart_mem_atlas H _
  have h_iff := ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas
    (I := I) (n := ∞) hOne hAtlas hy
  have hyEx : (chartAt H (x : M)).extend I (y : M) ∈
      frontier ((chartAt H (x : M)).extend I).target := h_iff.mp hyx
  have hExtend : (chartAt H (x : M)).extend I (y : M) = I (chartAt H (x : M) (y : M)) := rfl
  rw [hExtend] at hyEx
  by_contra hC
  have hInRange : I (chartAt H (x : M) (y : M)) ∈ Set.range I := mem_range_self _
  have hClosure : I (chartAt H (x : M) (y : M)) ∈ closure (Set.range I) := subset_closure hInRange
  have hC' : I (chartAt H (x : M) (y : M)) ∉ frontier (Set.range I) := hC
  rw [frontier, Set.mem_diff] at hC'
  push Not at hC'
  have hI_int : I (chartAt H (x : M) (y : M)) ∈ interior (Set.range I) := hC' hClosure
  have h_target_int :
      I (chartAt H (x : M) (y : M)) ∈ interior ((chartAt H (x : M)).extend I).target :=
    (chartAt H (x : M)).mem_interior_extend_target
      ((chartAt H (x : M)).map_source hy) hI_int
  exact (disjoint_interior_frontier
      (s := ((chartAt H (x : M)).extend I).target)).le_bot
    (show I (chartAt H (x : M) (y : M)) ∈ _ ∩ _ from ⟨h_target_int, hyEx⟩)

theorem exists_inclH_chart_eq
    {x y : BoundaryManifold I M}
    (hy : (y : M) ∈ (chartAt H (x : M)).source) :
    ∃ z : hI.boundaryH, hI.inclH z = chartAt H (x : M) (y : M) := by
  have hF : I (chartAt H (x : M) (y : M)) ∈ frontier (Set.range I) :=
    extChart_mem_frontier_of_mem_source (I := I) hy
  exact (HasSmoothBoundary.mem_range_inclH_iff (I := I) _).mpr hF

theorem inclH_boundaryChartFun_apply [Nonempty hI.boundaryH]
    {x y : BoundaryManifold I M}
    (hy : (y : M) ∈ (chartAt H (x : M)).source) :
    hI.inclH (boundaryChartFun (I := I) x y) = chartAt H (x : M) (y : M) := by
  unfold boundaryChartFun
  exact Function.invFun_eq (exists_inclH_chart_eq (I := I) hy)

theorem boundaryChartInvFun_val_of_mem_target
    (x : BoundaryManifold I M)
    {z : hI.boundaryH} (hz : z ∈ boundaryChartTarget (I := I) x) :
    ((boundaryChartInvFun (I := I) x z) : M) =
      (chartAt H (x : M)).symm (hI.inclH z) := by
  unfold boundaryChartInvFun
  have hz_target : hI.inclH z ∈ (chartAt H (x : M)).target := hz
  have h_pre_in_source : (chartAt H (x : M)).symm (hI.inclH z) ∈
      (chartAt H (x : M)).source := (chartAt H (x : M)).map_target hz_target
  have h_chart_eq :
      chartAt H (x : M) ((chartAt H (x : M)).symm (hI.inclH z)) = hI.inclH z :=
    (chartAt H (x : M)).right_inv hz_target
  have h_image_in_frontier :
      I (chartAt H (x : M) ((chartAt H (x : M)).symm (hI.inclH z))) ∈
        frontier (Set.range I) := by
    rw [h_chart_eq]
    exact (HasSmoothBoundary.mem_range_inclH_iff (I := I) _).mp ⟨z, rfl⟩
  have hOne : (∞ : WithTop ℕ∞) ≠ 0 := infty_ne_zero_withTopENat
  have hAtlas : chartAt H (x : M) ∈ atlas H M := chart_mem_atlas H _
  have h_iff := ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas
    (I := I) (n := ∞) hOne hAtlas h_pre_in_source
  have hExtendEq :
      (chartAt H (x : M)).extend I ((chartAt H (x : M)).symm (hI.inclH z)) =
        I (chartAt H (x : M) ((chartAt H (x : M)).symm (hI.inclH z))) := rfl
  have hExtFrontier :
      (chartAt H (x : M)).extend I ((chartAt H (x : M)).symm (hI.inclH z)) ∈
        frontier ((chartAt H (x : M)).extend I).target := by
    rw [hExtendEq]
    by_contra hC
    have h_in_target :
        I (chartAt H (x : M) ((chartAt H (x : M)).symm (hI.inclH z))) ∈
          ((chartAt H (x : M)).extend I).target := by
      rw [OpenPartialHomeomorph.extend_target]
      refine ⟨?_, mem_range_self _⟩
      simp only [mem_preimage, ModelWithCorners.left_inv]
      rw [h_chart_eq]
      exact hz_target
    have h_closure : I (chartAt H (x : M) ((chartAt H (x : M)).symm (hI.inclH z))) ∈
        closure ((chartAt H (x : M)).extend I).target := subset_closure h_in_target
    rw [frontier, Set.mem_diff] at hC
    push Not at hC
    have h_int : I (chartAt H (x : M) ((chartAt H (x : M)).symm (hI.inclH z))) ∈
        interior ((chartAt H (x : M)).extend I).target := hC h_closure
    have h_int_range :=
      OpenPartialHomeomorph.interior_extend_target_subset_interior_range _ h_int
    exact (disjoint_interior_frontier (s := Set.range I)).le_bot
      (show I (chartAt H (x : M) ((chartAt H (x : M)).symm (hI.inclH z))) ∈ _ ∩ _ from
        ⟨h_int_range, h_image_in_frontier⟩)
  have h_isBP : I.IsBoundaryPoint ((chartAt H (x : M)).symm (hI.inclH z)) :=
    h_iff.mpr hExtFrontier
  have h_in_boundary : (chartAt H (x : M)).symm (hI.inclH z) ∈ I.boundary M := h_isBP
  rw [dif_pos h_in_boundary]

theorem boundaryChartFun_mapsTo [Nonempty hI.boundaryH]
    (x : BoundaryManifold I M) :
    Set.MapsTo (boundaryChartFun (I := I) x) (boundaryChartSource (I := I) x)
      (boundaryChartTarget (I := I) x) := by
  intro y hy
  unfold boundaryChartTarget
  have h_eq := inclH_boundaryChartFun_apply (I := I) (x := x) (y := y) hy
  rw [Set.mem_preimage, h_eq]
  exact (chartAt H (x : M)).map_source hy

theorem boundaryChartInvFun_mapsTo
    (x : BoundaryManifold I M) :
    Set.MapsTo (boundaryChartInvFun (I := I) x) (boundaryChartTarget (I := I) x)
      (boundaryChartSource (I := I) x) := by
  intro z hz
  unfold boundaryChartSource
  rw [Set.mem_setOf_eq, boundaryChartInvFun_val_of_mem_target (I := I) x hz]
  exact (chartAt H (x : M)).map_target hz

theorem boundaryChart_left_inv [Nonempty hI.boundaryH]
    (x : BoundaryManifold I M) {y : BoundaryManifold I M}
    (hy : y ∈ boundaryChartSource (I := I) x) :
    boundaryChartInvFun (I := I) x (boundaryChartFun (I := I) x y) = y := by
  have hy' : (y : M) ∈ (chartAt H (x : M)).source := hy
  have hF := inclH_boundaryChartFun_apply (I := I) (x := x) (y := y) hy'
  have hzMaps := boundaryChartFun_mapsTo (I := I) x hy
  apply ext
  rw [boundaryChartInvFun_val_of_mem_target (I := I) x hzMaps]
  rw [hF]
  exact (chartAt H (x : M)).left_inv hy'

theorem boundaryChart_right_inv [Nonempty hI.boundaryH]
    (x : BoundaryManifold I M) {z : hI.boundaryH}
    (hz : z ∈ boundaryChartTarget (I := I) x) :
    boundaryChartFun (I := I) x (boundaryChartInvFun (I := I) x z) = z := by
  unfold boundaryChartFun
  have h_val : ((boundaryChartInvFun (I := I) x z) : M) =
      (chartAt H (x : M)).symm (hI.inclH z) :=
    boundaryChartInvFun_val_of_mem_target (I := I) x hz
  rw [h_val]
  rw [(chartAt H (x : M)).right_inv hz]
  exact Function.leftInverse_invFun hI.inclH_injective z

theorem continuousOn_boundaryChartFun [Nonempty hI.boundaryH]
    (x : BoundaryManifold I M) :
    ContinuousOn (boundaryChartFun (I := I) x) (boundaryChartSource (I := I) x) := by
  rw [hI.inclH_isInducing.continuousOn_iff]
  have h_cont :
      ContinuousOn (fun y : BoundaryManifold I M => chartAt H (x : M) (y : M))
        (boundaryChartSource (I := I) x) :=
    ((chartAt H (x : M)).continuousOn).comp
      continuous_subtype_val.continuousOn (fun _ hy => hy)
  refine h_cont.congr ?_
  intro y hy
  change (hI.inclH ∘ boundaryChartFun (I := I) x) y = chartAt H (x : M) (y : M)
  simp only [Function.comp_apply]
  exact inclH_boundaryChartFun_apply (I := I) (x := x) (y := y) hy

theorem continuousOn_boundaryChartInvFun
    (x : BoundaryManifold I M) :
    ContinuousOn (boundaryChartInvFun (I := I) x) (boundaryChartTarget (I := I) x) := by
  rw [continuousOn_iff_continuous_restrict]
  have h_underlying : Continuous
      (fun w : (boundaryChartTarget (I := I) x) =>
        (chartAt H (x : M)).symm (hI.inclH (w : hI.boundaryH))) := by
    have h_chart_symm_on : ContinuousOn (chartAt H (x : M)).symm
        (chartAt H (x : M)).target := (chartAt H (x : M)).continuousOn_symm
    have h_inclH_subtype : Continuous
        (fun u : (boundaryChartTarget (I := I) x) => hI.inclH (u : hI.boundaryH)) :=
      hI.inclH_continuous.comp continuous_subtype_val
    have h_maps : ∀ u : (boundaryChartTarget (I := I) x),
        hI.inclH (u : hI.boundaryH) ∈ (chartAt H (x : M)).target := fun u => u.2
    exact h_chart_symm_on.comp_continuous h_inclH_subtype h_maps
  have h_in_boundary : ∀ w : (boundaryChartTarget (I := I) x),
      (chartAt H (x : M)).symm (hI.inclH (w : hI.boundaryH)) ∈ I.boundary M := by
    intro w
    have hz : (w : hI.boundaryH) ∈ boundaryChartTarget (I := I) x := w.2
    have h_invFun_val :=
      boundaryChartInvFun_val_of_mem_target (I := I) x hz
    have hb : ((boundaryChartInvFun (I := I) x w) : M) ∈ I.boundary M :=
      (boundaryChartInvFun (I := I) x w).2
    rw [← h_invFun_val]
    exact hb
  have h_lifted : Continuous fun w : (boundaryChartTarget (I := I) x) =>
      (⟨(chartAt H (x : M)).symm (hI.inclH (w : hI.boundaryH)),
        h_in_boundary w⟩ : BoundaryManifold I M) :=
    h_underlying.subtype_mk h_in_boundary
  refine h_lifted.congr ?_
  intro w
  apply ext
  exact (boundaryChartInvFun_val_of_mem_target (I := I) x w.2).symm

def boundaryChart [Nonempty hI.boundaryH] (x : BoundaryManifold I M) :
    OpenPartialHomeomorph (BoundaryManifold I M) hI.boundaryH where
  toFun := boundaryChartFun (I := I) x
  invFun := boundaryChartInvFun (I := I) x
  source := boundaryChartSource (I := I) x
  target := boundaryChartTarget (I := I) x
  map_source' := boundaryChartFun_mapsTo (I := I) x
  map_target' := boundaryChartInvFun_mapsTo (I := I) x
  left_inv' := fun _ hy => boundaryChart_left_inv (I := I) x hy
  right_inv' := fun _ hz => boundaryChart_right_inv (I := I) x hz
  open_source := isOpen_boundaryChartSource (I := I) x
  open_target := isOpen_boundaryChartTarget (I := I) x
  continuousOn_toFun := continuousOn_boundaryChartFun (I := I) x
  continuousOn_invFun := continuousOn_boundaryChartInvFun (I := I) x

@[simp]
theorem boundaryChart_apply [Nonempty hI.boundaryH] (x y : BoundaryManifold I M) :
    boundaryChart (I := I) x y = boundaryChartFun (I := I) x y := rfl

@[simp]
theorem boundaryChart_source_eq [Nonempty hI.boundaryH] (x : BoundaryManifold I M) :
    (boundaryChart (I := I) x).source = boundaryChartSource (I := I) x := rfl

@[simp]
theorem boundaryChart_target_eq [Nonempty hI.boundaryH] (x : BoundaryManifold I M) :
    (boundaryChart (I := I) x).target = boundaryChartTarget (I := I) x := rfl

@[simp]
theorem boundaryChart_symm_apply [Nonempty hI.boundaryH] (x : BoundaryManifold I M)
    (z : hI.boundaryH) :
    (boundaryChart (I := I) x).symm z = boundaryChartInvFun (I := I) x z := rfl

omit hI [IsManifold I ∞ M] in
theorem mem_boundaryChartSource_self (x : BoundaryManifold I M) :
    x ∈ boundaryChartSource (I := I) x := by
  unfold boundaryChartSource
  exact mem_chart_source H _

theorem inclH_boundaryChart_apply [Nonempty hI.boundaryH]
    (x y : BoundaryManifold I M)
    (hy : (y : M) ∈ (chartAt H (x : M)).source) :
    hI.inclH (boundaryChart (I := I) x y) = chartAt H (x : M) (y : M) := by
  change hI.inclH (boundaryChartFun (I := I) x y) = chartAt H (x : M) (y : M)
  exact inclH_boundaryChartFun_apply (I := I) (x := x) (y := y) hy

omit [IsManifold I ∞ M] in
theorem isEmpty_of_isEmpty_boundaryH [IsEmpty hI.boundaryH] :
    IsEmpty (BoundaryManifold I M) := by
  refine ⟨fun y => ?_⟩
  have hyx : I.IsBoundaryPoint (y : M) := y.2
  have h_ext : extChartAt I (y : M) (y : M) ∈ frontier (Set.range I) := hyx
  have h_compute : extChartAt I (y : M) (y : M) = I (chartAt H (y : M) (y : M)) := rfl
  rw [h_compute] at h_ext
  rw [← hI.range_I_inclH] at h_ext
  obtain ⟨z, _⟩ := h_ext
  exact IsEmpty.false z

def defaultBoundaryChart (x : BoundaryManifold I M) :
    OpenPartialHomeomorph (BoundaryManifold I M) hI.boundaryH := by
  classical
  by_cases h : Nonempty hI.boundaryH
  · haveI : Nonempty hI.boundaryH := h
    exact boundaryChart (I := I) x
  · haveI hEmpty : IsEmpty hI.boundaryH := not_nonempty_iff.mp h
    haveI : IsEmpty (BoundaryManifold I M) := isEmpty_of_isEmpty_boundaryH (I := I)
    exact
      { toFun := fun w => (IsEmpty.false w).elim
        invFun := fun z => (hEmpty.false z).elim
        source := ∅
        target := ∅
        map_source' := fun _ h => h.elim
        map_target' := fun z _ => (hEmpty.false z).elim
        left_inv' := fun _ h => h.elim
        right_inv' := fun z _ => (hEmpty.false z).elim
        open_source := isOpen_empty
        open_target := isOpen_empty
        continuousOn_toFun := continuousOn_empty _
        continuousOn_invFun := continuousOn_empty _ }

theorem defaultBoundaryChart_eq_boundaryChart [Nonempty hI.boundaryH]
    (x : BoundaryManifold I M) :
    defaultBoundaryChart (I := I) x = boundaryChart (I := I) x := by
  unfold defaultBoundaryChart
  rw [dif_pos ‹_›]

instance chartedSpace : ChartedSpace hI.boundaryH (BoundaryManifold I M) where
  atlas := Set.range (fun x : BoundaryManifold I M => defaultBoundaryChart (I := I) x)
  chartAt x := defaultBoundaryChart (I := I) x
  mem_chart_source := fun x => by
    by_cases h : Nonempty hI.boundaryH
    · haveI : Nonempty hI.boundaryH := h
      rw [defaultBoundaryChart_eq_boundaryChart (I := I) x]
      change x ∈ (boundaryChart (I := I) x).source
      rw [boundaryChart_source_eq]
      exact mem_boundaryChartSource_self (I := I) x
    · haveI : IsEmpty hI.boundaryH := not_nonempty_iff.mp h
      haveI : IsEmpty (BoundaryManifold I M) := isEmpty_of_isEmpty_boundaryH (I := I)
      exact (IsEmpty.false x).elim
  chart_mem_atlas := fun x => ⟨x, rfl⟩

theorem chartedSpace_atlas :
    @atlas hI.boundaryH _ (BoundaryManifold I M) _ chartedSpace =
      Set.range (fun x : BoundaryManifold I M => defaultBoundaryChart (I := I) x) := rfl

omit hI [IsManifold I ∞ M] in
theorem range_coe_eq_boundary :
    Set.range ((↑) : BoundaryManifold I M → M) = I.boundary M := by
  ext y
  refine ⟨?_, fun hy => ?_⟩
  · rintro ⟨z, rfl⟩
    exact z.2
  · exact ⟨⟨y, hy⟩, rfl⟩

instance instSigmaCompactSpace [SigmaCompactSpace M] :
    SigmaCompactSpace (BoundaryManifold I M) := by
  have hOne : (∞ : WithTop ℕ∞) ≠ 0 := infty_ne_zero_withTopENat
  have h_closed : IsClosed (I.boundary M) :=
    ModelWithCorners.isClosed_boundary (I := I) (n := ∞) hOne
  exact h_closed.sigmaCompactSpace

theorem inclH_boundaryChart_eq_chart_subtype_val [Nonempty hI.boundaryH]
    (x : BoundaryManifold I M)
    {y : BoundaryManifold I M}
    (hy : y ∈ boundaryChartSource (I := I) x) :
    hI.inclH (boundaryChart (I := I) x y) = chartAt H (x : M) (y : M) :=
  inclH_boundaryChart_apply (I := I) x y hy

theorem inclH_boundaryChart_symm_apply [Nonempty hI.boundaryH]
    (x : BoundaryManifold I M)
    {z : hI.boundaryH} (hz : z ∈ boundaryChartTarget (I := I) x) :
    chartAt H (x : M) ((boundaryChart (I := I) x).symm z : M) = hI.inclH z := by
  have h_val : ((boundaryChart (I := I) x).symm z : M) =
      (chartAt H (x : M)).symm (hI.inclH z) := by
    change ((boundaryChartInvFun (I := I) x z) : M) =
        (chartAt H (x : M)).symm (hI.inclH z)
    exact boundaryChartInvFun_val_of_mem_target (I := I) x hz
  rw [h_val]
  exact (chartAt H (x : M)).right_inv hz

theorem inclH_boundaryChart_trans_apply [Nonempty hI.boundaryH]
    (x x' : BoundaryManifold I M)
    {z : hI.boundaryH}
    (hz_target : z ∈ boundaryChartTarget (I := I) x')
    (hz_source : ((boundaryChart (I := I) x').symm z) ∈ boundaryChartSource (I := I) x) :
    hI.inclH ((boundaryChart (I := I) x).toFun ((boundaryChart (I := I) x').symm z)) =
      chartAt H (x : M)
        ((chartAt H (x' : M)).symm (hI.inclH z)) := by
  have h1 : chartAt H (x' : M) (((boundaryChart (I := I) x').symm z) : M) =
      hI.inclH z := inclH_boundaryChart_symm_apply (I := I) x' hz_target
  have h2 : hI.inclH ((boundaryChart (I := I) x).toFun
        ((boundaryChart (I := I) x').symm z)) =
      chartAt H (x : M) (((boundaryChart (I := I) x').symm z) : M) :=
    inclH_boundaryChart_apply (I := I) x _ hz_source
  rw [h2]
  have h3 : (((boundaryChart (I := I) x').symm z) : M) =
      (chartAt H (x' : M)).symm (hI.inclH z) := by
    change ((boundaryChartInvFun (I := I) x' z) : M) =
        (chartAt H (x' : M)).symm (hI.inclH z)
    exact boundaryChartInvFun_val_of_mem_target (I := I) x' hz_target
  rw [h3]

theorem boundaryI_trans_eq_projE_extend [Nonempty hI.boundaryH]
    (x x' : BoundaryManifold I M) {e : hI.boundaryE}
    (hz_target : hI.boundaryI.symm e ∈ boundaryChartTarget (I := I) x')
    (hz_source : ((boundaryChart (I := I) x').symm (hI.boundaryI.symm e)) ∈
      boundaryChartSource (I := I) x) :
    hI.boundaryI ((boundaryChart (I := I) x).toFun
        ((boundaryChart (I := I) x').symm (hI.boundaryI.symm e))) =
      hI.projE ((chartAt H (x : M)).extend I
        (((chartAt H (x' : M)).extend I).symm
          (I (hI.inclH (hI.boundaryI.symm e))))) := by
  set y : H := hI.inclH (hI.boundaryI.symm e) with hy_def
  have h_extend_symm :
      ((chartAt H (x' : M)).extend I).symm (I y) =
        (chartAt H (x' : M)).symm y := by
    change (chartAt H (x' : M)).symm (I.symm (I y)) = (chartAt H (x' : M)).symm y
    rw [I.left_inv y]
  rw [h_extend_symm]
  have h_extend :
      (chartAt H (x : M)).extend I ((chartAt H (x' : M)).symm y) =
        I (chartAt H (x : M) ((chartAt H (x' : M)).symm y)) := rfl
  rw [h_extend]
  have h_inclH_trans :
      hI.inclH ((boundaryChart (I := I) x).toFun
          ((boundaryChart (I := I) x').symm (hI.boundaryI.symm e))) =
        chartAt H (x : M) ((chartAt H (x' : M)).symm y) := by
    have := inclH_boundaryChart_trans_apply (I := I) x x'
      (z := hI.boundaryI.symm e) hz_target hz_source
    convert this using 2
  have h_proj :
      hI.projE (I (hI.inclH ((boundaryChart (I := I) x).toFun
          ((boundaryChart (I := I) x').symm (hI.boundaryI.symm e))))) =
        hI.boundaryI ((boundaryChart (I := I) x).toFun
          ((boundaryChart (I := I) x').symm (hI.boundaryI.symm e))) :=
    hI.proj_inclH_compat _
  rw [← h_proj, h_inclH_trans]

theorem contDiffOn_boundaryChart_trans [Nonempty hI.boundaryH]
    (x x' : BoundaryManifold I M) :
    ContDiffOn ℝ ∞
      (hI.boundaryI ∘ ((boundaryChart (I := I) x').symm ≫ₕ
        boundaryChart (I := I) x) ∘ hI.boundaryI.symm)
      (hI.boundaryI.symm ⁻¹'
        ((boundaryChart (I := I) x').symm ≫ₕ boundaryChart (I := I) x).source ∩
        Set.range hI.boundaryI) := by
  have h_range_univ : Set.range hI.boundaryI = Set.univ := hI.boundaryI.range_eq_univ
  set TE : E → E := fun w =>
    (chartAt H (x : M)).extend I
      (((chartAt H (x' : M)).extend I).symm w)
  have hAtlasA : chartAt H (x : M) ∈ atlas H M := chart_mem_atlas H _
  have hAtlasA' : chartAt H (x' : M) ∈ atlas H M := chart_mem_atlas H _
  have hT_ambient_trans : (chartAt H (x' : M)).symm ≫ₕ chartAt H (x : M) ∈
      contDiffGroupoid ∞ I :=
    StructureGroupoid.compatible (contDiffGroupoid ∞ I) hAtlasA' hAtlasA
  have hT_ambient_property := mem_groupoid_of_pregroupoid.mp hT_ambient_trans
  obtain ⟨h_TE_smooth, _⟩ := hT_ambient_property
  set S_ambient : Set E :=
    I.symm ⁻¹' ((chartAt H (x' : M)).symm ≫ₕ chartAt H (x : M)).source ∩ Set.range I
    with hS_ambient_def
  have hT_ambient :
      ContDiffOn ℝ ∞
        ((I : H → E) ∘ ((chartAt H (x' : M)).symm ≫ₕ chartAt H (x : M)) ∘ I.symm)
        S_ambient := h_TE_smooth
  have hTE_eq : (fun w => (chartAt H (x : M)).extend I
          (((chartAt H (x' : M)).extend I).symm w)) =
      ((I : H → E) ∘ ((chartAt H (x' : M)).symm ≫ₕ chartAt H (x : M)) ∘ I.symm) := by
    funext w
    simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.coe_trans]
  have hTE_smooth : ContDiffOn ℝ ∞ TE S_ambient := by
    rw [show TE = (fun w => (chartAt H (x : M)).extend I
        (((chartAt H (x' : M)).extend I).symm w)) from rfl, hTE_eq]
    exact hT_ambient
  set S_boundary : Set hI.boundaryE :=
    hI.boundaryI.symm ⁻¹'
      ((boundaryChart (I := I) x').symm ≫ₕ boundaryChart (I := I) x).source ∩
      Set.range hI.boundaryI with hS_boundary_def
  have hMaps : Set.MapsTo
      (fun e : hI.boundaryE => I (hI.inclH (hI.boundaryI.symm e)))
      S_boundary S_ambient := by
    intro e he
    have he_src : hI.boundaryI.symm e ∈
        ((boundaryChart (I := I) x').symm ≫ₕ boundaryChart (I := I) x).source := he.1
    rw [OpenPartialHomeomorph.trans_source] at he_src
    obtain ⟨he_target, he_src_in_chart⟩ := he_src
    have he_target' : hI.boundaryI.symm e ∈ (boundaryChart (I := I) x').target := he_target
    have he_src_in_chart' :
        (boundaryChart (I := I) x').symm (hI.boundaryI.symm e) ∈
          (boundaryChart (I := I) x).source := he_src_in_chart
    rw [boundaryChart_target_eq] at he_target'
    rw [boundaryChart_source_eq] at he_src_in_chart'
    have h_inclH_target : hI.inclH (hI.boundaryI.symm e) ∈ (chartAt H (x' : M)).target :=
      he_target'
    refine ⟨?_, mem_range_self _⟩
    rw [Set.mem_preimage]
    rw [I.left_inv]
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · exact h_inclH_target
    · have h_val_eq : ((boundaryChart (I := I) x').symm (hI.boundaryI.symm e) : M) =
          (chartAt H (x' : M)).symm (hI.inclH (hI.boundaryI.symm e)) := by
        change ((boundaryChartInvFun (I := I) x' (hI.boundaryI.symm e)) : M) =
            (chartAt H (x' : M)).symm (hI.inclH (hI.boundaryI.symm e))
        exact boundaryChartInvFun_val_of_mem_target (I := I) x' he_target
      rw [Set.mem_preimage, ← h_val_eq]
      exact he_src_in_chart'
  have h_inner_smooth : ContDiff ℝ ∞
      (fun e : hI.boundaryE => I (hI.inclH (hI.boundaryI.symm e))) :=
    hI.I_inclH_boundaryI_symm_contDiff
  have h_TE_comp : ContDiffOn ℝ ∞
      (fun e : hI.boundaryE => TE (I (hI.inclH (hI.boundaryI.symm e))))
      S_boundary :=
    hTE_smooth.comp h_inner_smooth.contDiffOn hMaps
  have h_proj_smooth : ContDiff ℝ ∞ hI.projE := hI.projE_contDiff
  have h_full : ContDiffOn ℝ ∞
      (fun e : hI.boundaryE =>
        hI.projE (TE (I (hI.inclH (hI.boundaryI.symm e)))))
      S_boundary :=
    h_proj_smooth.contDiffOn.comp h_TE_comp (Set.mapsTo_univ _ _)
  refine h_full.congr ?_
  intro e he
  have he_src : hI.boundaryI.symm e ∈
      ((boundaryChart (I := I) x').symm ≫ₕ boundaryChart (I := I) x).source := he.1
  rw [OpenPartialHomeomorph.trans_source] at he_src
  obtain ⟨he_target, he_src_in_chart⟩ := he_src
  have he_target' : hI.boundaryI.symm e ∈ (boundaryChart (I := I) x').target := he_target
  rw [boundaryChart_target_eq] at he_target'
  have he_src_in_chart' :
      (boundaryChart (I := I) x').symm (hI.boundaryI.symm e) ∈
        (boundaryChart (I := I) x).source := he_src_in_chart
  rw [boundaryChart_source_eq] at he_src_in_chart'
  have h_factor := boundaryI_trans_eq_projE_extend (I := I) x x'
    (e := e) he_target' he_src_in_chart'
  change hI.boundaryI (((boundaryChart (I := I) x').symm ≫ₕ boundaryChart (I := I) x)
      (hI.boundaryI.symm e)) = hI.projE (TE (I (hI.inclH (hI.boundaryI.symm e))))
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  exact h_factor

instance isManifold : IsManifold hI.boundaryI ∞ (BoundaryManifold I M) := by
  by_cases h : Nonempty hI.boundaryH
  · haveI hN : Nonempty hI.boundaryH := h
    apply isManifold_of_contDiffOn
    intro e e' he he'
    rw [chartedSpace_atlas (I := I) (M := M)] at he he'
    obtain ⟨x', hx'⟩ := he
    obtain ⟨x, hx⟩ := he'
    simp only at hx hx'
    rw [defaultBoundaryChart_eq_boundaryChart (I := I) x'] at hx'
    rw [defaultBoundaryChart_eq_boundaryChart (I := I) x] at hx
    subst hx'
    subst hx
    exact contDiffOn_boundaryChart_trans (I := I) x x'
  · haveI : IsEmpty hI.boundaryH := not_nonempty_iff.mp h
    haveI : IsEmpty (BoundaryManifold I M) := isEmpty_of_isEmpty_boundaryH (I := I)
    infer_instance

end BoundaryManifold

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
