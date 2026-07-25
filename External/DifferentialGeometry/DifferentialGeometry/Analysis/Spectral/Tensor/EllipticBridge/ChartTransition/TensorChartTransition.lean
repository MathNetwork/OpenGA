import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorReprFromFrame
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.Hom


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

@[reducible] private def rsTriv (r s : ℕ) (α : M) :
    Trivialization (TensorRSModel r s ℝ E)
      (Bundle.TotalSpace.proj (F := TensorRSModel r s ℝ E)
        (E := fun y : M => TensorRSSpace r s I y)) :=
  trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma rsTriv_baseSet (r s : ℕ) (α : M) :
    (rsTriv (E := E) (I := I) (M := M) r s α).baseSet = (chartAt H α).source := by
  classical
  change ((trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) α).baseSet) =
    (chartAt H α).source
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
      (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
  rw [Set.inter_self]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorTrivProj_eq_clmAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (x : M) :
    tensorTrivProj (I := I) (M := M) g r s S α x =
      (rsTriv (E := E) (I := I) (M := M) r s α).continuousLinearMapAt ℝ x
        (S.toSection x) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma coordChangeL_apply_eq_clmAt_symmL
    (r s : ℕ) (γ α : M) {x : M}
    (hxγ : x ∈ (chartAt H γ).source) (hxα : x ∈ (chartAt H α).source)
    (w : TensorRSModel r s ℝ E) :
    ((rsTriv (E := E) (I := I) (M := M) r s γ).coordChangeL ℝ
        (rsTriv (E := E) (I := I) (M := M) r s α) x) w =
      (rsTriv (E := E) (I := I) (M := M) r s α).continuousLinearMapAt ℝ x
        ((rsTriv (E := E) (I := I) (M := M) r s γ).symmL ℝ x w) := by
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  letI : TopologicalSpace (TotalSpace (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y)) :=
    tensorRSBundle_topology r s
  letI : FiberBundle (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_fiber r s
  letI : VectorBundle ℝ (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_vector r s
  have hxγ' : x ∈ (rsTriv (E := E) (I := I) (M := M) r s γ).baseSet := by
    rw [rsTriv_baseSet]; exact hxγ
  have hxα' : x ∈ (rsTriv (E := E) (I := I) (M := M) r s α).baseSet := by
    rw [rsTriv_baseSet]; exact hxα
  rw [Bundle.Trivialization.coordChangeL_apply _ _ ⟨hxγ', hxα'⟩,
    Bundle.Trivialization.continuousLinearMapAt_apply,
    Bundle.Trivialization.coe_linearMapAt_of_mem _ hxα',
    Bundle.Trivialization.symmL_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorTrivProj_chartTransition
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (γ α : M) {x : M}
    (hxγ : x ∈ (chartAt H γ).source) (hxα : x ∈ (chartAt H α).source) :
    tensorTrivProj (I := I) (M := M) g r s S α x =
      ((rsTriv (E := E) (I := I) (M := M) r s γ).coordChangeL ℝ
          (rsTriv (E := E) (I := I) (M := M) r s α) x)
        (tensorTrivProj (I := I) (M := M) g r s S γ x) := by
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  letI : TopologicalSpace (TotalSpace (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y)) :=
    tensorRSBundle_topology r s
  letI : FiberBundle (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_fiber r s
  letI : VectorBundle ℝ (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_vector r s
  have hxγ' : x ∈ (rsTriv (E := E) (I := I) (M := M) r s γ).baseSet := by
    rw [rsTriv_baseSet]; exact hxγ
  rw [tensorTrivProj_eq_clmAt (I := I) (M := M) g r s S γ x,
    coordChangeL_apply_eq_clmAt_symmL (E := E) (I := I) (M := M) r s γ α
      hxγ hxα]
  rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hxγ' (S.toSection x)]
  exact (tensorTrivProj_eq_clmAt (I := I) (M := M) g r s S α x)

def transitionCoeff
    (r s : ℕ) (γ α : M)
    (P₀ Q : TensorCompIdx (E := E) r s) (x : M) : ℝ :=
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  letI : TopologicalSpace (TotalSpace (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y)) :=
    tensorRSBundle_topology r s
  letI : FiberBundle (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_fiber r s
  letI : VectorBundle ℝ (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_vector r s
  tensorChartComponentProjection (E := E) r s P₀.1 P₀.2
    (((rsTriv (E := E) (I := I) (M := M) r s γ).coordChangeL ℝ
        (rsTriv (E := E) (I := I) (M := M) r s α) x)
      (tensorChartBasisElement (E := E) r s Q.1 Q.2))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma contMDiffOn_rsCoordChangeL (r s : ℕ) (γ α : M) :
    ContMDiffOn I (modelWithCornersSelf ℝ
        (TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)) ∞
      (fun x : M =>
        ((rsTriv (E := E) (I := I) (M := M) r s γ).coordChangeL ℝ
          (rsTriv (E := E) (I := I) (M := M) r s α) x :
          TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E))
      ((chartAt H γ).source ∩ (chartAt H α).source) := by
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  letI : TopologicalSpace (TotalSpace (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y)) :=
    tensorRSBundle_topology r s
  letI : FiberBundle (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_fiber r s
  letI : VectorBundle ℝ (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) :=
    tensorRSBundle_vector r s
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) I :=
    tensorRSBundle_smooth ∞ r s
  have h := contMDiffOn_coordChangeL (n := (∞ : WithTop ℕ∞)) (IB := I)
    (F := TensorRSModel r s ℝ E)
    (E := fun y : M => TensorRSSpace r s I y)
    (rsTriv (E := E) (I := I) (M := M) r s γ)
    (rsTriv (E := E) (I := I) (M := M) r s α)
  rwa [rsTriv_baseSet, rsTriv_baseSet] at h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma contMDiffOn_transitionCoeff
    (r s : ℕ) (γ α : M) (P₀ Q : TensorCompIdx (E := E) r s) :
    ContMDiffOn I (modelWithCornersSelf ℝ ℝ) ∞
      (transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q)
      ((chartAt H γ).source ∩ (chartAt H α).source) := by
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  have hcoord := contMDiffOn_rsCoordChangeL (E := E) (I := I) (M := M) r s γ α
  have hcoord_app : ContMDiffOn I
      (modelWithCornersSelf ℝ (TensorRSModel r s ℝ E)) ∞
      (fun x : M =>
        ((rsTriv (E := E) (I := I) (M := M) r s γ).coordChangeL ℝ
          (rsTriv (E := E) (I := I) (M := M) r s α) x :
          TensorRSModel r s ℝ E →L[ℝ] TensorRSModel r s ℝ E)
            (tensorChartBasisElement (E := E) r s Q.1 Q.2))
      ((chartAt H γ).source ∩ (chartAt H α).source) :=
    hcoord.clm_apply contMDiffOn_const
  have hproj : ContMDiff
      (modelWithCornersSelf ℝ (TensorRSModel r s ℝ E))
      (modelWithCornersSelf ℝ ℝ) ∞
      (tensorChartComponentProjection (E := E) r s P₀.1 P₀.2) :=
    (tensorChartComponentProjection (E := E) r s P₀.1 P₀.2).contMDiff
  exact hproj.comp_contMDiffOn hcoord_app

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_eq_transitionCoeff_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (γ α : M)
    (P₀ : TensorCompIdx (E := E) r s)
    {x : M} (hx : x ∈ (chartAt H γ).source ∩ (chartAt H α).source) :
    tensorChartComponentRaw (I := I) (M := M) g r s S α P₀.1 P₀.2 x =
      ∑ Q : TensorCompIdx (E := E) r s,
        transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q x *
          tensorChartComponentRaw (I := I) (M := M) g r s S γ Q.1 Q.2 x := by
  classical
  letI : NormedAddCommGroup (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedAddCommGroup r s
  letI : NormedSpace ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_normedSpace r s
  obtain ⟨hxγ, hxα⟩ := hx
  rw [tensorChartComponentRaw_def (I := I) (M := M) g r s S α P₀.1 P₀.2]
  rw [tensorTrivProj_chartTransition (E := E) (I := I) (M := M)
    g r s S γ α hxγ hxα]
  set L : TensorRSModel r s ℝ E ≃L[ℝ] TensorRSModel r s ℝ E :=
    (rsTriv (E := E) (I := I) (M := M) r s γ).coordChangeL ℝ
      (rsTriv (E := E) (I := I) (M := M) r s α) x with hL_def
  have hsum := tensorRSModel_eq_sum_basis (E := E) r s
    (tensorTrivProj (I := I) (M := M) g r s S γ x)
  conv_lhs => rw [hsum]
  rw [show (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
              tensorChartComponentProjection (E := E) r s Idx Jdx
                  (tensorTrivProj (I := I) (M := M) g r s S γ x) •
                tensorChartBasisElement (E := E) r s Idx Jdx) =
        ∑ Q : TensorCompIdx (E := E) r s,
          tensorChartComponentProjection (E := E) r s Q.1 Q.2
              (tensorTrivProj (I := I) (M := M) g r s S γ x) •
            tensorChartBasisElement (E := E) r s Q.1 Q.2 from
    (Finset.sum_product'
      (s := (Finset.univ : Finset (Fin r → Fin (Module.finrank ℝ E))))
      (t := (Finset.univ : Finset (Fin s → Fin (Module.finrank ℝ E))))
      (f := fun Idx Jdx =>
        tensorChartComponentProjection (E := E) r s Idx Jdx
            (tensorTrivProj (I := I) (M := M) g r s S γ x) •
          tensorChartBasisElement (E := E) r s Idx Jdx)).symm]
  rw [map_sum L, map_sum (tensorChartComponentProjection (E := E) r s P₀.1 P₀.2)]
  refine Finset.sum_congr rfl ?_
  intro Q _
  rw [map_smul L, map_smul (tensorChartComponentProjection (E := E) r s P₀.1 P₀.2),
    smul_eq_mul]
  rw [show tensorChartComponentProjection (E := E) r s P₀.1 P₀.2
          (L (tensorChartBasisElement (E := E) r s Q.1 Q.2)) =
        transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q x from by
      rw [hL_def]; rfl]
  rw [tensorChartComponentRaw_def (I := I) (M := M) g r s S γ Q.1 Q.2]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem tensorChartComponentRaw_chartTransition_decomp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (γ α : M)
    (P₀ : TensorCompIdx (E := E) r s) :
    ∃ c : TensorCompIdx (E := E) r s → M → ℝ,
      (∀ Q, ContMDiffOn I (modelWithCornersSelf ℝ ℝ) ∞ (c Q)
        ((chartAt H γ).source ∩ (chartAt H α).source)) ∧
      ∀ x ∈ (chartAt H γ).source ∩ (chartAt H α).source,
        tensorChartComponentRaw (I := I) (M := M) g r s S α P₀.1 P₀.2 x =
          ∑ Q : TensorCompIdx (E := E) r s,
            c Q x *
              tensorChartComponentRaw (I := I) (M := M) g r s S γ Q.1 Q.2 x := by
  classical
  refine ⟨transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀, ?_, ?_⟩
  · intro Q
    exact contMDiffOn_transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q
  · intro x hx
    exact tensorChartComponentRaw_eq_transitionCoeff_sum
      (E := E) (I := I) (M := M) g r s S γ α P₀ hx

section UniformBound

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma pouTsupport_inter_isCompact (γ α : M) :
    IsCompact
      (tsupport (fun x : M =>
          ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
        tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (pouTsupport_isCompact (I := I) (M := M) γ).inter_right
    (isClosed_tsupport _)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pouTsupport_subset_chartSource (γ : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H γ).source :=
  DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M γ

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pouTsupport_inter_subset_chartSource_inter (γ α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H γ).source ∩ (chartAt H α).source := by
  intro x hx
  exact ⟨pouTsupport_subset_chartSource (I := I) (M := M) γ hx.1,
    pouTsupport_subset_chartSource (I := I) (M := M) α hx.2⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma exists_transitionCoeff_bound_on_pouTsupport_pair
    (r s : ℕ) (γ α : M) (P₀ Q : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        |transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q b| ≤ C := by
  classical
  set K : Set M := tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_def
  by_cases hK_empty : K = ∅
  · refine ⟨0, le_refl 0, ?_⟩
    intro b hb
    rw [hK_empty] at hb
    exact absurd hb (Set.notMem_empty b)
  · have hK_ne : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
    have hK_compact : IsCompact K :=
      pouTsupport_inter_isCompact (I := I) (M := M) γ α
    have hK_sub : K ⊆ (chartAt H γ).source ∩ (chartAt H α).source :=
      pouTsupport_inter_subset_chartSource_inter (I := I) (M := M) γ α
    have h_cont_overlap : ContinuousOn
        (transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q)
        ((chartAt H γ).source ∩ (chartAt H α).source) :=
      (contMDiffOn_transitionCoeff (E := E) (I := I) (M := M)
        r s γ α P₀ Q).continuousOn
    have h_cont_K : ContinuousOn
        (transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q) K :=
      h_cont_overlap.mono hK_sub
    have h_abs_cont_K : ContinuousOn
        (fun b => |transitionCoeff (E := E) (I := I) (M := M)
          r s γ α P₀ Q b|) K :=
      continuous_abs.comp_continuousOn h_cont_K
    obtain ⟨b_max, _hb_max_mem, hb_max⟩ :=
      hK_compact.exists_isMaxOn hK_ne h_abs_cont_K
    set C₀ : ℝ := |transitionCoeff (E := E) (I := I) (M := M)
      r s γ α P₀ Q b_max| with hC₀_def
    have hC₀_nn : 0 ≤ C₀ := abs_nonneg _
    refine ⟨C₀, hC₀_nn, ?_⟩
    intro b hb
    exact hb_max hb

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartAtlasPOU_tsupport_eq_empty_of_notMem_finset
    {γ : M} (hγ : γ ∉ chartAtlasPOU_finset (I := I) (M := M)) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
  classical
  have h_supp_empty :
      Function.support (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
    ext x
    simp only [Function.mem_support, ne_eq, Set.mem_empty_iff_false, iff_false,
      Decidable.not_not]
    exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_weight_zero_of_notMem
      (I := I) (M := M) hγ x
  unfold tsupport
  rw [h_supp_empty, closure_empty]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma pouTsupport_inter_eq_empty_of_left_notMem_finset
    {γ : M} (hγ : γ ∉ chartAtlasPOU_finset (I := I) (M := M)) (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
  rw [chartAtlasPOU_tsupport_eq_empty_of_notMem_finset
    (I := I) (M := M) hγ]
  exact Set.empty_inter _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma pouTsupport_inter_eq_empty_of_right_notMem_finset
    (γ : M) {α : M} (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M)) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) = ∅ := by
  rw [chartAtlasPOU_tsupport_eq_empty_of_notMem_finset
    (I := I) (M := M) hα]
  exact Set.inter_empty _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma exists_transitionCoeff_bound_on_pouTsupport_joint_PQ
    (r s : ℕ) (γ α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ P₀ Q : TensorCompIdx (E := E) r s,
      ∀ b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        |transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q b| ≤ C := by
  classical
  suffices h_aux :
      ∀ T : Finset (TensorCompIdx (E := E) r s × TensorCompIdx (E := E) r s),
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ PQ ∈ T,
          ∀ b ∈ tsupport (fun x : M =>
                ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
              tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
            |transitionCoeff (E := E) (I := I) (M := M)
              r s γ α PQ.1 PQ.2 b| ≤ C by
    obtain ⟨C, hC_nn, hC_le⟩ := h_aux
      (Finset.univ : Finset (TensorCompIdx (E := E) r s ×
        TensorCompIdx (E := E) r s))
    refine ⟨C, hC_nn, ?_⟩
    intro P₀ Q b hb
    exact hC_le (P₀, Q) (Finset.mem_univ _) b hb
  intro T
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨0, le_refl 0, ?_⟩
    intro PQ hPQ
    exact absurd hPQ (Finset.notMem_empty _)
  | insert PQ T' _hPQ_notin ih =>
    obtain ⟨C_T, hC_T_nn, hC_T_le⟩ := ih
    obtain ⟨C_PQ, hC_PQ_nn, hC_PQ_le⟩ :=
      exists_transitionCoeff_bound_on_pouTsupport_pair
        (E := E) (I := I) (M := M) r s γ α PQ.1 PQ.2
    refine ⟨max C_T C_PQ, le_max_of_le_left hC_T_nn, ?_⟩
    intro QQ hQQ b hb
    rcases Finset.mem_insert.mp hQQ with heq | hin
    · subst heq
      exact le_trans (hC_PQ_le b hb) (le_max_right _ _)
    · exact le_trans (hC_T_le QQ hin b hb) (le_max_left _ _)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma exists_transitionCoeff_uniform_bound_on_pouTsupport
    (r s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ γ α : M, ∀ P₀ Q : TensorCompIdx (E := E) r s, ∀ b : M,
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        |transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q b| ≤ K := by
  classical
  suffices h_aux :
      ∀ S : Finset (M × M),
        ∃ K : ℝ, 0 ≤ K ∧
          ∀ γα ∈ S,
          ∀ P₀ Q : TensorCompIdx (E := E) r s, ∀ b : M,
            b ∈ tsupport (fun x : M =>
                ((chartAtlasPOU I M γα.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
              tsupport (fun x : M =>
                ((chartAtlasPOU I M γα.2 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
            |transitionCoeff (E := E) (I := I) (M := M)
              r s γα.1 γα.2 P₀ Q b| ≤ K by
    obtain ⟨K, hK_nn, hK_le⟩ := h_aux
      (chartAtlasPOU_finset (I := I) (M := M) ×ˢ
        chartAtlasPOU_finset (I := I) (M := M))
    refine ⟨K, hK_nn, ?_⟩
    intro γ α P₀ Q b hb
    by_cases hγ : γ ∈ chartAtlasPOU_finset (I := I) (M := M)
    · by_cases hα : α ∈ chartAtlasPOU_finset (I := I) (M := M)
      · have hmem : (γ, α) ∈
            chartAtlasPOU_finset (I := I) (M := M) ×ˢ
              chartAtlasPOU_finset (I := I) (M := M) :=
          Finset.mem_product.mpr ⟨hγ, hα⟩
        exact hK_le (γ, α) hmem P₀ Q b hb
      · have h_empty := pouTsupport_inter_eq_empty_of_right_notMem_finset
          (I := I) (M := M) γ hα
        rw [h_empty] at hb
        exact absurd hb (Set.notMem_empty b)
    · have h_empty := pouTsupport_inter_eq_empty_of_left_notMem_finset
        (I := I) (M := M) hγ α
      rw [h_empty] at hb
      exact absurd hb (Set.notMem_empty b)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, le_refl 0, ?_⟩
    intro γα hγα
    exact absurd hγα (Finset.notMem_empty _)
  | insert γα S' _hγα_notin ih =>
    obtain ⟨K_S, hK_S_nn, hK_S_le⟩ := ih
    obtain ⟨K_γα, hK_γα_nn, hK_γα_le⟩ :=
      exists_transitionCoeff_bound_on_pouTsupport_joint_PQ
        (E := E) (I := I) (M := M) r s γα.1 γα.2
    refine ⟨max K_S K_γα, le_max_of_le_left hK_S_nn, ?_⟩
    intro δβ hδβ P₀ Q b hb
    rcases Finset.mem_insert.mp hδβ with heq | hin
    · subst heq
      exact le_trans (hK_γα_le P₀ Q b hb) (le_max_right _ _)
    · exact le_trans (hK_S_le δβ hin P₀ Q b hb) (le_max_left _ _)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem transitionCoeff_le_uniform_on_pouTsupport
    (r s : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ γ α : M, ∀ P₀ Q : TensorCompIdx (E := E) r s, ∀ b : M,
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        |transitionCoeff (E := E) (I := I) (M := M) r s γ α P₀ Q b| ≤ K :=
  exists_transitionCoeff_uniform_bound_on_pouTsupport
    (E := E) (I := I) (M := M) r s

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma isOpen_extCoordChange_source (γ α : M) :
    IsOpen (((extChartAt I γ).symm ≫ extChartAt I α).source) := by
  classical
  rw [ext_coord_change_source (I := I) α γ, I.image_eq, I.range_eq_univ,
    Set.inter_univ]
  exact ((chartAt H γ).symm ≫ₕ chartAt H α).open_source.preimage I.continuous_symm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma pouTsupport_inter_image_extChartAt_isCompact (γ α : M) :
    IsCompact
      ((extChartAt I γ) '' (tsupport (fun x : M =>
          ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
        tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))) := by
  classical
  have hK_compact : IsCompact (tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    pouTsupport_inter_isCompact (I := I) (M := M) γ α
  have h_cont : ContinuousOn (extChartAt I γ) (chartAt H γ).source := by
    have h := continuousOn_extChartAt (I := I) γ
    rw [extChartAt_source (I := I)] at h
    exact h
  have hK_sub : tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H γ).source := fun x hx =>
    pouTsupport_subset_chartSource (I := I) (M := M) γ hx.1
  exact hK_compact.image_of_continuousOn (h_cont.mono hK_sub)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma extChartAt_mem_extCoordChange_source
    {γ α : M} {b : M}
    (hbγ : b ∈ (chartAt H γ).source) (hbα : b ∈ (chartAt H α).source) :
    extChartAt I γ b ∈ ((extChartAt I γ).symm ≫ extChartAt I α).source := by
  classical
  have h_img := OpenPartialHomeomorph.extend_image_source_inter
    (I := I) (f := chartAt H γ) (f' := chartAt H α)
  change extChartAt I γ b ∈ (I.extendCoordChange (chartAt H γ) (chartAt H α)).source
  rw [← h_img]
  exact ⟨b, ⟨hbγ, hbα⟩, rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma pouTsupport_inter_image_subset_extCoordChange_source
    (γ α : M) :
    (extChartAt I γ) '' (tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) ⊆
      ((extChartAt I γ).symm ≫ extChartAt I α).source := by
  classical
  rintro z ⟨b, hb, rfl⟩
  have hb_inter : b ∈ (chartAt H γ).source ∩ (chartAt H α).source :=
    pouTsupport_inter_subset_chartSource_inter (I := I) (M := M) γ α hb
  exact extChartAt_mem_extCoordChange_source
    (I := I) (M := M) hb_inter.1 hb_inter.2

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_fderiv_chartTransition_bound_on_pouTsupport_pair
    (γ α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        ‖fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm)
            (extChartAt I γ b)‖ ≤ C := by
  classical
  set U : Set E := ((extChartAt I γ).symm ≫ extChartAt I α).source with hU_def
  have hU_open : IsOpen U :=
    isOpen_extCoordChange_source (I := I) (M := M) γ α
  have h_contDiff : ContDiffOn ℝ ∞
      (extChartAt I α ∘ (extChartAt I γ).symm) U :=
    contDiffOn_ext_coord_change (I := I) (n := ∞) α γ
  have h_one_le : (1 : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (by decide : (1 : ℕ∞) ≤ ⊤)
  have h_cont_fderiv : ContinuousOn
      (fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm)) U :=
    h_contDiff.continuousOn_fderiv_of_isOpen hU_open h_one_le
  have h_cont_norm : ContinuousOn
      (fun y : E => ‖fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm) y‖) U :=
    continuous_norm.comp_continuousOn h_cont_fderiv
  set K_E : Set E := (extChartAt I γ) '' (tsupport (fun x : M =>
        ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) with hKE_def
  have hKE_compact : IsCompact K_E :=
    pouTsupport_inter_image_extChartAt_isCompact (I := I) (M := M) γ α
  have hKE_subset_U : K_E ⊆ U :=
    pouTsupport_inter_image_subset_extCoordChange_source (I := I) (M := M) γ α
  by_cases hKE_empty : K_E = ∅
  · refine ⟨0, le_refl 0, ?_⟩
    intro b hb
    have h_mem : extChartAt I γ b ∈ K_E := ⟨b, hb, rfl⟩
    rw [hKE_empty] at h_mem
    exact absurd h_mem (Set.notMem_empty _)
  · have hKE_ne : K_E.Nonempty := Set.nonempty_iff_ne_empty.mpr hKE_empty
    have h_cont_norm_KE : ContinuousOn
        (fun y : E => ‖fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm) y‖)
        K_E := h_cont_norm.mono hKE_subset_U
    obtain ⟨y_max, _hy_mem, hy_max⟩ :=
      hKE_compact.exists_isMaxOn hKE_ne h_cont_norm_KE
    set C₀ : ℝ := ‖fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm) y_max‖
      with hC₀_def
    have hC₀_nn : 0 ≤ C₀ := norm_nonneg _
    refine ⟨C₀, hC₀_nn, ?_⟩
    intro b hb
    have h_mem : extChartAt I γ b ∈ K_E := ⟨b, hb, rfl⟩
    exact hy_max h_mem

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_fderiv_chartTransition_uniform_bound_on_pouTsupport :
    ∃ K_jac : ℝ, 0 ≤ K_jac ∧
      ∀ γ α : M, ∀ b : M,
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm)
            (extChartAt I γ b)‖ ≤ K_jac := by
  classical
  suffices h_aux :
      ∀ S : Finset (M × M),
        ∃ K_jac : ℝ, 0 ≤ K_jac ∧
          ∀ γα ∈ S, ∀ b : M,
            b ∈ tsupport (fun x : M =>
                ((chartAtlasPOU I M γα.1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
              tsupport (fun x : M =>
                ((chartAtlasPOU I M γα.2 : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
            ‖fderiv ℝ (extChartAt I γα.2 ∘ (extChartAt I γα.1).symm)
                (extChartAt I γα.1 b)‖ ≤ K_jac by
    obtain ⟨K_jac, hK_nn, hK_le⟩ := h_aux
      (chartAtlasPOU_finset (I := I) (M := M) ×ˢ
        chartAtlasPOU_finset (I := I) (M := M))
    refine ⟨K_jac, hK_nn, ?_⟩
    intro γ α b hb
    by_cases hγ : γ ∈ chartAtlasPOU_finset (I := I) (M := M)
    · by_cases hα : α ∈ chartAtlasPOU_finset (I := I) (M := M)
      · have hmem : (γ, α) ∈
            chartAtlasPOU_finset (I := I) (M := M) ×ˢ
              chartAtlasPOU_finset (I := I) (M := M) :=
          Finset.mem_product.mpr ⟨hγ, hα⟩
        exact hK_le (γ, α) hmem b hb
      · have h_empty := pouTsupport_inter_eq_empty_of_right_notMem_finset
          (I := I) (M := M) γ hα
        rw [h_empty] at hb
        exact absurd hb (Set.notMem_empty b)
    · have h_empty := pouTsupport_inter_eq_empty_of_left_notMem_finset
        (I := I) (M := M) hγ α
      rw [h_empty] at hb
      exact absurd hb (Set.notMem_empty b)
  intro S
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, le_refl 0, ?_⟩
    intro γα hγα
    exact absurd hγα (Finset.notMem_empty _)
  | insert γα S' _hγα_notin ih =>
    obtain ⟨K_S, hK_S_nn, hK_S_le⟩ := ih
    obtain ⟨K_γα, hK_γα_nn, hK_γα_le⟩ :=
      exists_fderiv_chartTransition_bound_on_pouTsupport_pair
        (E := E) (I := I) (M := M) γα.1 γα.2
    refine ⟨max K_S K_γα, le_max_of_le_left hK_S_nn, ?_⟩
    intro δβ hδβ b hb
    rcases Finset.mem_insert.mp hδβ with heq | hin
    · subst heq
      exact le_trans (hK_γα_le b hb) (le_max_right _ _)
    · exact le_trans (hK_S_le δβ hin b hb) (le_max_left _ _)

omit [NeZero (Module.finrank ℝ E)] in
theorem chartTransition_fderiv_le_uniform_on_pouTsupport :
    ∃ K_jac : ℝ, 0 ≤ K_jac ∧
      ∀ γ α : M, ∀ b : M,
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖fderiv ℝ (extChartAt I α ∘ (extChartAt I γ).symm)
            (extChartAt I γ b)‖ ≤ K_jac :=
  exists_fderiv_chartTransition_uniform_bound_on_pouTsupport
    (E := E) (I := I) (M := M)

end UniformBound

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
