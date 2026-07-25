import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SChartParallelExtend
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SCovariantDerivative
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SIntrinsicChartRank0


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
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private lemma chartTensor0SParallelExtend_zero_scalar_pullback_eventuallyEq
    (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (T₀ : Tensor0SSpace 0 I b) :
    (fun b' : M =>
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b') ℝ from
          chartTensor0SParallelExtend (I := I) 0 α b T₀ b')
          (fun i : Fin 0 => Fin.elim0 i)) ∘ (extChartAt I α).symm
      =ᶠ[𝓝 (extChartAt I α b)]
      (fun _ : E =>
        ((trivializationAt (Tensor0SModel 0 ℝ E)
            (fun y : M => Tensor0SSpace 0 I y) α).continuousLinearMapAt ℝ b T₀)
          (fun i : Fin 0 => Fin.elim0 i)) := by
  classical
  have hpull :=
    chartTensor0SParallelExtend_repr_eventuallyEq_const (I := I) (r := 0) α hb T₀
  set e := trivializationAt (Tensor0SModel 0 ℝ E)
    (fun y : M => Tensor0SSpace 0 I y) α with he_def
  have hU_open : IsOpen e.baseSet := e.open_baseSet
  have hb_U : b ∈ e.baseSet :=
    chartLeviCivitaGoodSet_mem_tensor0S_baseSet (I := I) (r := 0) hb
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
  filter_upwards [hU_preim_nhds, hint_nhds, hpull] with y hy_U _hy_int hy_repr
  set b' : M := (extChartAt I α).symm y with hb'_def
  have hb'_U : b' ∈ e.baseSet := hy_U
  change (show ContinuousMultilinearMap ℝ
        (fun _ : Fin 0 => TangentSpace I b') ℝ from
      chartTensor0SParallelExtend (I := I) 0 α b T₀ b')
      (fun i : Fin 0 => Fin.elim0 i) =
    (e.continuousLinearMapAt ℝ b T₀) (fun i : Fin 0 => Fin.elim0 i)
  have happly :=
    tensor0SChartE_section_repr_apply_tuple (I := I) (n := 0) α
      (T := chartTensor0SParallelExtend (I := I) 0 α b T₀) hb'_U
      (fun i : Fin 0 => Fin.elim0 i)
  have htuple_eq :
      (fun i : Fin 0 => trivFromE (I := I) α b' (Fin.elim0 i)) =
        (fun i : Fin 0 => Fin.elim0 i) := by
    funext i; exact i.elim0
  rw [htuple_eq] at happly
  rw [← happly]
  change (tensor0SChartE_section_repr (I := I) 0 α
        (chartTensor0SParallelExtend (I := I) 0 α b T₀) b')
      (fun i : Fin 0 => Fin.elim0 i) =
    (e.continuousLinearMapAt ℝ b T₀) (fun i : Fin 0 => Fin.elim0 i)
  rw [show tensor0SChartE_section_repr (I := I) 0 α
        (chartTensor0SParallelExtend (I := I) 0 α b T₀) b' =
      e.continuousLinearMapAt ℝ b T₀ from hy_repr]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartTensor0SParallelExtend_zero_scalar_apply
    (α : M) {b b' : M} (T₀ : Tensor0SSpace 0 I b)
    (hb' : b' ∈ (trivializationAt (Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SSpace 0 I y) α).baseSet) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin 0 => TangentSpace I b') ℝ from
      chartTensor0SParallelExtend (I := I) 0 α b T₀ b')
        (fun i : Fin 0 => Fin.elim0 i) =
      ((trivializationAt (Tensor0SModel 0 ℝ E)
          (fun y : M => Tensor0SSpace 0 I y) α).continuousLinearMapAt ℝ b T₀)
        (fun i : Fin 0 => Fin.elim0 i) := by
  classical
  have hb'_tan : b' ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    change b' ∈ (trivializationAt (Tensor0SModel 0 ℝ E)
      (fun y : M => Tensor0SSpace 0 I y) α).baseSet
    exact hb'
  have happly :=
    tensor0SChartE_section_repr_apply_tuple (I := I) (n := 0) α
      (T := chartTensor0SParallelExtend (I := I) 0 α b T₀) hb'_tan
      (fun i : Fin 0 => Fin.elim0 i)
  have htuple_eq :
      (fun i : Fin 0 => trivFromE (I := I) α b' (Fin.elim0 i)) =
        (fun i : Fin 0 => Fin.elim0 i) := by
    funext i; exact i.elim0
  rw [htuple_eq] at happly
  rw [← happly]
  have hrepr := chartTensor0SE_section_repr_chartTensor0SParallelExtend
    (I := I) 0 α b T₀ hb'
  change (tensor0SChartE_section_repr (I := I) 0 α
        (chartTensor0SParallelExtend (I := I) 0 α b T₀) b')
      (fun i : Fin 0 => Fin.elim0 i) =
    ((trivializationAt (Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SSpace 0 I y) α).continuousLinearMapAt ℝ b T₀)
      (fun i : Fin 0 => Fin.elim0 i)
  rw [hrepr]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartTensor0SParallelExtend_zero_scalar_mdifferentiableAt
    (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (T₀ : Tensor0SSpace 0 I b) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun b' : M =>
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b') ℝ from
          chartTensor0SParallelExtend (I := I) 0 α b T₀ b')
          (fun i : Fin 0 => Fin.elim0 i)) b := by
  classical
  set e := trivializationAt (Tensor0SModel 0 ℝ E)
    (fun y : M => Tensor0SSpace 0 I y) α with he_def
  have hb_U : b ∈ e.baseSet :=
    chartLeviCivitaGoodSet_mem_tensor0S_baseSet (I := I) (r := 0) hb
  have hbase_nhds : e.baseSet ∈ 𝓝 b := e.open_baseSet.mem_nhds hb_U
  set c : ℝ := (e.continuousLinearMapAt ℝ b T₀)
    (fun i : Fin 0 => Fin.elim0 i) with hc_def
  have hev :
      (fun b' : M =>
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b') ℝ from
          chartTensor0SParallelExtend (I := I) 0 α b T₀ b')
          (fun i : Fin 0 => Fin.elim0 i)) =ᶠ[𝓝 b] (fun _ : M => c) := by
    filter_upwards [hbase_nhds] with b' hb'_U
    exact chartTensor0SParallelExtend_zero_scalar_apply
      (I := I) α (b := b) (b' := b') T₀ hb'_U
  exact (mdifferentiableAt_const).congr_of_eventuallyEq hev

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartTensor0SParallelExtend_zero_scalar_mfderiv_eq_zero
    (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (T₀ : Tensor0SSpace 0 I b) (v : TangentSpace I b) :
    mfderiv I 𝓘(ℝ)
      (fun b' : M =>
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b') ℝ from
          chartTensor0SParallelExtend (I := I) 0 α b T₀ b')
          (fun i : Fin 0 => Fin.elim0 i)) b v = 0 := by
  classical
  set φ := extChartAt I α
  set scalarFn : M → ℝ := fun b' : M =>
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin 0 => TangentSpace I b') ℝ from
      chartTensor0SParallelExtend (I := I) 0 α b T₀ b')
      (fun i : Fin 0 => Fin.elim0 i)
  have hev : scalarFn ∘ φ.symm =ᶠ[𝓝 (φ b)]
      (fun _ : E =>
        ((trivializationAt (Tensor0SModel 0 ℝ E)
            (fun y : M => Tensor0SSpace 0 I y) α).continuousLinearMapAt ℝ b T₀)
          (fun i : Fin 0 => Fin.elim0 i)) :=
    chartTensor0SParallelExtend_zero_scalar_pullback_eventuallyEq
      (I := I) α hb T₀
  have hb_src_chart : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
  have hb_tgt_int : φ b ∈ interior (φ.target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hFderiv : fderiv ℝ (scalarFn ∘ φ.symm) (φ b) = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq hev]
    exact fderiv_const_apply _
  have hscalarFn_at : MDifferentiableAt I 𝓘(ℝ) scalarFn b :=
    chartTensor0SParallelExtend_zero_scalar_mdifferentiableAt
      (I := I) α hb T₀
  have hkey := mfderiv_scalar_eq_chart_fderiv (I := I) α scalarFn (x := b)
    hb_src_chart hb_tgt_int hscalarFn_at v
  rw [hkey, hFderiv]
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartTensor0SCovariantDerivative_chartTensor0SParallelExtend_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (T₀ : Tensor0SSpace 0 I b)
    (X : Π b' : M, TangentSpace I b') :
    chartTensor0SCovariantDerivative (I := I) 0 g α
        (chartTensor0SParallelExtend (I := I) 0 α b T₀) X b =
      - (∑ k : Fin 0,
          chartTensor0SSlotCorrection (I := I) 0 g α
            (chartTensor0SParallelExtend (I := I) 0 α b T₀) X b k) := by
  classical
  have hRHS_zero :
      (∑ k : Fin 0,
        chartTensor0SSlotCorrection (I := I) 0 g α
          (chartTensor0SParallelExtend (I := I) 0 α b T₀) X b k) =
      (0 : Tensor0SSpace 0 I b) := by
    apply Finset.sum_of_isEmpty
  rw [hRHS_zero, neg_zero]
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = (fun i : Fin 0 => Fin.elim0 i) := by
    funext i; exact i.elim0
  rw [hm]
  rw [chartTensor0SCovariantDerivative_zero_apply (I := I) g α
      (chartTensor0SParallelExtend (I := I) 0 α b T₀) X b
      (fun i : Fin 0 => Fin.elim0 i)]
  change mfderiv I 𝓘(ℝ) _ b (X b) = (0 : Tensor0SSpace 0 I b)
      (fun i : Fin 0 => Fin.elim0 i)
  rw [ContinuousMultilinearMap.zero_apply]
  exact chartTensor0SParallelExtend_zero_scalar_mfderiv_eq_zero
    (I := I) α hb T₀ (X b)

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private lemma tensor0SIntrinsicChartCLM_chartTensor0SParallelExtend_eq_zero
    (r : ℕ) (α : M) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (T₀ : Tensor0SSpace r I b) :
    tensor0SIntrinsicChartCLM (I := I) r α
        (chartTensor0SParallelExtend (I := I) r α b T₀) b = 0 := by
  classical
  unfold tensor0SIntrinsicChartCLM
  rw [chartTensor0SParallelExtend_repr_pullback_fderiv_eq_zero
      (I := I) r α hb T₀]
  ext v
  simp

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem chartTensor0SCovariantDerivative_chartTensor0SParallelExtend_succ
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (T₀ : Tensor0SSpace (s + 1) I b)
    (X : Π b' : M, TangentSpace I b') :
    chartTensor0SCovariantDerivative (I := I) (s + 1) g α
        (chartTensor0SParallelExtend (I := I) (s + 1) α b T₀) X b =
      - (∑ k : Fin (s + 1),
          chartTensor0SSlotCorrection (I := I) (s + 1) g α
            (chartTensor0SParallelExtend (I := I) (s + 1) α b T₀) X b k) := by
  classical
  rw [chartTensor0SCovariantDerivative_succ (I := I) s g α
      (chartTensor0SParallelExtend (I := I) (s + 1) α b T₀) X b]
  have hintr : tensor0SIntrinsicChartCLM (I := I) (s + 1) α
      (chartTensor0SParallelExtend (I := I) (s + 1) α b T₀) b (X b) = 0 := by
    rw [tensor0SIntrinsicChartCLM_chartTensor0SParallelExtend_eq_zero
      (I := I) (s + 1) α hb T₀]
    rfl
  rw [hintr]
  rw [zero_sub]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem chartTensor0SCovariantDerivative_chartTensor0SParallelExtend
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (T₀ : Tensor0SSpace r I b)
    (X : Π b' : M, TangentSpace I b') :
    chartTensor0SCovariantDerivative (I := I) r g α
        (chartTensor0SParallelExtend (I := I) r α b T₀) X b =
      - (∑ k : Fin r,
          chartTensor0SSlotCorrection (I := I) r g α
            (chartTensor0SParallelExtend (I := I) r α b T₀) X b k) := by
  classical
  match r with
  | 0 =>
      exact chartTensor0SCovariantDerivative_chartTensor0SParallelExtend_zero
        (I := I) g α hb T₀ X
  | s + 1 =>
      exact chartTensor0SCovariantDerivative_chartTensor0SParallelExtend_succ
        (I := I) g s α hb T₀ X

end Connection
end Integral
end DifferentialGeometry

end
