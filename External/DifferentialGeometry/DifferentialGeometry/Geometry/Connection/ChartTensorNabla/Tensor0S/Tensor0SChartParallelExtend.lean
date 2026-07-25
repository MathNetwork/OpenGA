import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SCovariantDerivative
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SChartChristoffel
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartTorsion


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff
open Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

noncomputable def chartTensor0SParallelExtend
    (r : ℕ) (α b : M) (T₀ : Tensor0SSpace r I b) :
    Π b' : M, Tensor0SSpace r I b' :=
  fun b' =>
    (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b'
      ((trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).continuousLinearMapAt ℝ b T₀)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SParallelExtend_apply
    (r : ℕ) (α b : M) (T₀ : Tensor0SSpace r I b) (b' : M) :
    chartTensor0SParallelExtend (I := I) r α b T₀ b' =
      (trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).symmL ℝ b'
        ((trivializationAt (Tensor0SModel r ℝ E)
            (fun y : M => Tensor0SSpace r I y) α).continuousLinearMapAt ℝ b T₀) := rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SE_section_repr_chartTensor0SParallelExtend
    (r : ℕ) (α b : M) (T₀ : Tensor0SSpace r I b) {b' : M}
    (hb' : b' ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet) :
    tensor0SChartE_section_repr (I := I) r α
        (chartTensor0SParallelExtend (I := I) r α b T₀) b' =
      (trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).continuousLinearMapAt ℝ b T₀ := by
  classical
  set e := trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) α with he_def
  unfold tensor0SChartE_section_repr chartTensor0SParallelExtend
  exact (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).continuousLinearMapAt_symmL
    (R := ℝ) hb' _

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartLeviCivitaGoodSet_mem_tensor0S_baseSet
    {α x : M} (r : ℕ)
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    x ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet := by
  classical
  change x ∈ (trivializationAt E (TangentSpace I) α).baseSet
  exact chartLeviCivitaGoodSet_mem_baseSet (I := I) hx

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SParallelExtend_repr_eventuallyEq_const
    (r : ℕ) (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (T₀ : Tensor0SSpace r I b) :
    (tensor0SChartE_section_repr (I := I) r α
        (chartTensor0SParallelExtend (I := I) r α b T₀)) ∘ (extChartAt I α).symm
      =ᶠ[𝓝 (extChartAt I α b)]
      (fun _ : E => (trivializationAt (Tensor0SModel r ℝ E)
          (fun y : M => Tensor0SSpace r I y) α).continuousLinearMapAt ℝ b T₀) := by
  classical
  set e := trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) α with he_def
  have hU_open : IsOpen e.baseSet := e.open_baseSet
  have hb_U : b ∈ e.baseSet :=
    chartLeviCivitaGoodSet_mem_tensor0S_baseSet (I := I) r hb
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hb_int : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) :=
    isOpen_interior
  have hsymm_cont : ContinuousAt (extChartAt I α).symm (extChartAt I α b) :=
    continuousAt_extChartAt_symm' hb_src
  have hU_preim_nhds :
      (extChartAt I α).symm ⁻¹' e.baseSet ∈ 𝓝 (extChartAt I α b) := by
    apply hsymm_cont.preimage_mem_nhds
    have hxφ_inv : (extChartAt I α).symm (extChartAt I α b) = b :=
      (extChartAt I α).left_inv hb_src
    rw [hxφ_inv]
    exact hU_open.mem_nhds hb_U
  have hint_nhds : interior ((extChartAt I α).target : Set E) ∈
      𝓝 (extChartAt I α b) :=
    hint_open.mem_nhds hb_int
  filter_upwards [hU_preim_nhds, hint_nhds] with y hy_U _hy_int
  change tensor0SChartE_section_repr (I := I) r α
      (chartTensor0SParallelExtend (I := I) r α b T₀)
      ((extChartAt I α).symm y) =
    e.continuousLinearMapAt ℝ b T₀
  exact chartTensor0SE_section_repr_chartTensor0SParallelExtend
    (I := I) r α b T₀ hy_U

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SParallelExtend_repr_pullback_fderiv_eq_zero
    (r : ℕ) (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (T₀ : Tensor0SSpace r I b) :
    fderiv ℝ
        (tensor0SChartE_section_repr (I := I) r α
          (chartTensor0SParallelExtend (I := I) r α b T₀) ∘ (extChartAt I α).symm)
      (extChartAt I α b) = 0 := by
  classical
  have hev :=
    chartTensor0SParallelExtend_repr_eventuallyEq_const (I := I) r α hb T₀
  rw [Filter.EventuallyEq.fderiv_eq hev]
  exact fderiv_const_apply _

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SParallelExtend_repr_pullback_fderiv_apply_eq_zero
    (r : ℕ) (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (T₀ : Tensor0SSpace r I b) (w : E) :
    fderiv ℝ
        (tensor0SChartE_section_repr (I := I) r α
          (chartTensor0SParallelExtend (I := I) r α b T₀) ∘ (extChartAt I α).symm)
      (extChartAt I α b) w = 0 := by
  rw [chartTensor0SParallelExtend_repr_pullback_fderiv_eq_zero
        (I := I) r α hb T₀]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SParallelExtend_mdifferentiableAt
    (r : ℕ) (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (T₀ : Tensor0SSpace r I b) :
    letI _h_top : TopologicalSpace
        (TotalSpace (Tensor0SModel r ℝ E)
          (fun x : M => Tensor0SSpace r I x)) :=
      tensor0SBundle_topology r
    MDifferentiableAt I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E))
      (fun b' : M => TotalSpace.mk'
        (Tensor0SModel r ℝ E)
        (E := fun x : M => Tensor0SSpace r I x) b'
        (chartTensor0SParallelExtend (I := I) r α b T₀ b')) b := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x)) :=
    tensor0SBundle_topology r
  letI _h_fib : FiberBundle (Tensor0SModel r ℝ E)
      (fun x : M => Tensor0SSpace r I x) :=
    tensor0SBundle_fiber r
  set e := trivializationAt (Tensor0SModel r ℝ E)
    (fun y : M => Tensor0SSpace r I y) α with he_def
  have hb_base : b ∈ e.baseSet :=
    chartLeviCivitaGoodSet_mem_tensor0S_baseSet (I := I) r hb
  have hbase_open : IsOpen e.baseSet := e.open_baseSet
  have hbase_nhds : e.baseSet ∈ 𝓝 b := hbase_open.mem_nhds hb_base
  have hconst :
      (fun b' : M =>
          (e ⟨b', chartTensor0SParallelExtend (I := I) r α b T₀ b'⟩).2) =ᶠ[𝓝 b]
        (fun _ : M => e.continuousLinearMapAt ℝ b T₀) := by
    filter_upwards [hbase_nhds] with b' hb'
    have hcoe := e.coe_linearMapAt_of_mem (R := ℝ) (b := b') hb'
    have happ := congrFun hcoe
      (chartTensor0SParallelExtend (I := I) r α b T₀ b')
    change (e ⟨b', chartTensor0SParallelExtend (I := I) r α b T₀ b'⟩).2 =
      e.continuousLinearMapAt ℝ b T₀
    rw [← happ]
    change e.continuousLinearMapAt ℝ b'
        (chartTensor0SParallelExtend (I := I) r α b T₀ b') =
      e.continuousLinearMapAt ℝ b T₀
    change e.continuousLinearMapAt ℝ b'
        (e.symmL ℝ b' (e.continuousLinearMapAt ℝ b T₀)) =
      e.continuousLinearMapAt ℝ b T₀
    exact e.continuousLinearMapAt_symmL (R := ℝ) hb' _
  have hrep_diff :
      MDifferentiableAt I 𝓘(ℝ, Tensor0SModel r ℝ E)
        (fun b' : M =>
          (e ⟨b', chartTensor0SParallelExtend (I := I) r α b T₀ b'⟩).2) b :=
    (mdifferentiableAt_const (c := e.continuousLinearMapAt ℝ b T₀)).congr_of_eventuallyEq
      hconst
  exact (Trivialization.mdifferentiableAt_section_iff (IB := I) e
    (fun b' : M => chartTensor0SParallelExtend (I := I) r α b T₀ b') hb_base).mpr
    hrep_diff

end Connection
end Integral
end DifferentialGeometry
