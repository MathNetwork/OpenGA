import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SChartChristoffel
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SCovariantDerivative
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.TensorSectionMDifferentiability


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Topology
open Bundle Set Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

private noncomputable def evalEmptyCLM :
    Tensor0SModel 0 ℝ E →L[ℝ] ℝ :=
  ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) ℝ
    (fun i : Fin 0 => Fin.elim0 i)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
@[simp] private lemma evalEmptyCLM_apply (F : Tensor0SModel 0 ℝ E) :
    evalEmptyCLM (E := E) F = F (fun i : Fin 0 => Fin.elim0 i) := rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma tensor0SChartE_section_repr_zero_empty (α : M)
    (T : Π b' : M, Tensor0SSpace 0 I b') {b' : M}
    (hb' : b' ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (tensor0SChartE_section_repr (I := I) 0 α T b')
        (fun i : Fin 0 => Fin.elim0 i) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
        (fun i : Fin 0 => Fin.elim0 i) := by
  classical
  rw [tensor0SChartE_section_repr_apply_tuple (I := I) (n := 0) α T hb'
      (fun i : Fin 0 => Fin.elim0 i)]
  congr 1
  funext i
  exact i.elim0

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma tensor0SChartFiberFromModel_zero_empty (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (w : Tensor0SModel 0 ℝ E) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin 0 => TangentSpace I b) ℝ from
      tensor0SChartFiberFromModel (I := I) 0 α b w)
        (fun i : Fin 0 => Fin.elim0 i) =
      w (fun i : Fin 0 => Fin.elim0 i) := by
  classical
  unfold tensor0SChartFiberFromModel
  rw [tensor0SBundle_symmL_apply_eq_compContinuousLinearMap
    (I := I) (n := 0) α (b := b) hb w]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  exact i.elim0

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma chartE_eval_eq_scalar (α : M)
    (T : Π b' : M, Tensor0SSpace 0 I b') {b' : M}
    (hb' : b' ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    evalEmptyCLM (E := E) (tensor0SChartE_section_repr (I := I) 0 α T b') =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
        (fun i : Fin 0 => Fin.elim0 i) := by
  rw [evalEmptyCLM_apply]
  exact tensor0SChartE_section_repr_zero_empty (I := I) α T hb'

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma evalEmpty_chartPullback_eventually_eq_scalar
    (α : M) (T : Π b' : M, Tensor0SSpace 0 I b')
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (fun y : E =>
        evalEmptyCLM (E := E)
          ((tensor0SChartE_section_repr (I := I) 0 α T ∘
            (extChartAt I α).symm) y)) =ᶠ[𝓝 (extChartAt I α b)]
      (fun b' : M =>
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
            (fun i : Fin 0 => Fin.elim0 i)) ∘ (extChartAt I α).symm := by
  classical
  set φ := extChartAt I α
  have hBase_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hTgt_int_open : IsOpen (interior (φ.target : Set E)) := isOpen_interior
  have hb_src : b ∈ φ.source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hb_tgt_int : φ b ∈ interior (φ.target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hCont_on_int : ContinuousOn φ.symm (interior (φ.target : Set E)) :=
    (continuousOn_extChartAt_symm α).mono interior_subset
  have hOpen_inter :
      IsOpen (interior (φ.target : Set E) ∩
              φ.symm ⁻¹' (trivializationAt E (TangentSpace I) α).baseSet) :=
    hCont_on_int.isOpen_inter_preimage hTgt_int_open hBase_open
  have hMem :
      φ b ∈ interior (φ.target : Set E) ∩
              φ.symm ⁻¹' (trivializationAt E (TangentSpace I) α).baseSet := by
    refine ⟨hb_tgt_int, ?_⟩
    rw [Set.mem_preimage, φ.left_inv hb_src]
    exact hb_base
  refine Filter.eventually_of_mem (hOpen_inter.mem_nhds hMem) ?_
  rintro y ⟨_hy_int, hy_base⟩
  exact chartE_eval_eq_scalar (I := I) α T (b' := φ.symm y) hy_base

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma mdifferentiableAt_scalarFn_of_tensorSectionMDiffAt
    (α : M) (T : Π b' : M, Tensor0SSpace 0 I b')
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (hT_at : TensorSectionMDiffAt (I := I) 0 T b) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun b' : M =>
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
          (fun i : Fin 0 => Fin.elim0 i)) b := by
  classical
  set repr : M → Tensor0SModel 0 ℝ E :=
    tensor0SChartE_section_repr (I := I) 0 α T
  set scalarFn : M → ℝ := fun b' : M =>
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
      (fun i : Fin 0 => Fin.elim0 i)
  have hb_base_α : b ∈ (trivializationAt (Tensor0SModel 0 ℝ E)
      (fun y : M => Tensor0SSpace 0 I y) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hα_repr_diff : MDifferentiableAt I 𝓘(ℝ, Tensor0SModel 0 ℝ E)
      (fun b' : M =>
        ((trivializationAt (Tensor0SModel 0 ℝ E)
            (fun y : M => Tensor0SSpace 0 I y) α) ⟨b', T b'⟩).2) b :=
    (Bundle.Trivialization.mdifferentiableAt_section_iff (IB := I)
      (e := trivializationAt (Tensor0SModel 0 ℝ E)
        (fun y : M => Tensor0SSpace 0 I y) α) T hb_base_α).mp hT_at
  have hbase_α_nhds : (trivializationAt (Tensor0SModel 0 ℝ E)
      (fun y : M => Tensor0SSpace 0 I y) α).baseSet ∈ 𝓝 b :=
    (trivializationAt (Tensor0SModel 0 ℝ E)
      (fun y : M => Tensor0SSpace 0 I y) α).open_baseSet.mem_nhds hb_base_α
  have h_funeq :
      repr =ᶠ[𝓝 b]
        (fun b' : M =>
          ((trivializationAt (Tensor0SModel 0 ℝ E)
              (fun y : M => Tensor0SSpace 0 I y) α) ⟨b', T b'⟩).2) := by
    filter_upwards [hbase_α_nhds] with b' hb'
    have hcoe := (trivializationAt (Tensor0SModel 0 ℝ E)
      (fun y : M => Tensor0SSpace 0 I y) α).coe_linearMapAt_of_mem (R := ℝ) hb'
    exact (congrFun hcoe (T b'))
  have hrepr_at : MDifferentiableAt I 𝓘(ℝ, Tensor0SModel 0 ℝ E) repr b :=
    hα_repr_diff.congr_of_eventuallyEq h_funeq
  have hcomp : MDifferentiableAt I 𝓘(ℝ)
      ((evalEmptyCLM (E := E) : Tensor0SModel 0 ℝ E →L[ℝ] ℝ) ∘ repr) b :=
    (evalEmptyCLM (E := E)).mdifferentiableAt.comp (I' := 𝓘(ℝ, Tensor0SModel 0 ℝ E))
      b hrepr_at
  have hev :
      scalarFn =ᶠ[𝓝 b]
        (evalEmptyCLM (E := E) : Tensor0SModel 0 ℝ E →L[ℝ] ℝ) ∘ repr := by
    filter_upwards [hbase_α_nhds] with b' hb'
    change scalarFn b' = evalEmptyCLM (E := E) (repr b')
    rw [chartE_eval_eq_scalar (I := I) α T hb']
  exact hcomp.congr_of_eventuallyEq hev

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
theorem tensor0SIntrinsicChartCLM_zero_apply_empty_eq_mfderiv
    (α : M) (T : Π b' : M, Tensor0SSpace 0 I b')
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (hT_at : TensorSectionMDiffAt (I := I) 0 T b)
    (v : TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin 0 => TangentSpace I b) ℝ from
      tensor0SIntrinsicChartCLM (I := I) 0 α T b v)
        (fun i : Fin 0 => Fin.elim0 i) =
      mfderiv I 𝓘(ℝ) (fun b' : M =>
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
          (fun i : Fin 0 => Fin.elim0 i)) b v := by
  classical
  set φ := extChartAt I α
  set repr : M → Tensor0SModel 0 ℝ E :=
    tensor0SChartE_section_repr (I := I) 0 α T
  set scalarFn : M → ℝ := fun b' : M =>
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
      (fun i : Fin 0 => Fin.elim0 i)
  set v0 : E := trivToE (I := I) α b v
  have hb_src : b ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hb
  have hb_tgt_int : φ b ∈ interior (φ.target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  rw [tensor0SIntrinsicChartCLM_apply (I := I) 0 α T b v]
  rw [tensor0SChartFiberFromModel_zero_empty (I := I) α hb_base
      (fderiv ℝ (repr ∘ φ.symm) (φ b) v0)]
  change evalEmptyCLM (E := E) (fderiv ℝ (repr ∘ φ.symm) (φ b) v0) = _
  have hDiff_repr_pullback : DifferentiableAt ℝ (repr ∘ φ.symm) (φ b) :=
    differentiableAt_tensor0SChartE_pullback_of_mdifferentiableAt
      (I := I) 0 α T hb hT_at
  have hChain :
      fderiv ℝ ((evalEmptyCLM (E := E) : Tensor0SModel 0 ℝ E →L[ℝ] ℝ) ∘
            (repr ∘ φ.symm)) (φ b) =
        (evalEmptyCLM (E := E) : Tensor0SModel 0 ℝ E →L[ℝ] ℝ).comp
          (fderiv ℝ (repr ∘ φ.symm) (φ b)) := by
    rw [fderiv_comp (φ b)
        (evalEmptyCLM (E := E)).differentiableAt hDiff_repr_pullback]
    simp [ContinuousLinearMap.fderiv]
  have hCommute :
      evalEmptyCLM (E := E) (fderiv ℝ (repr ∘ φ.symm) (φ b) v0) =
        fderiv ℝ
            ((evalEmptyCLM (E := E) : Tensor0SModel 0 ℝ E →L[ℝ] ℝ) ∘
              (repr ∘ φ.symm)) (φ b) v0 := by
    rw [hChain]; rfl
  rw [hCommute]
  have hev :
      ((evalEmptyCLM (E := E) : Tensor0SModel 0 ℝ E →L[ℝ] ℝ) ∘
        (repr ∘ φ.symm)) =ᶠ[𝓝 (φ b)] (scalarFn ∘ φ.symm) :=
    evalEmpty_chartPullback_eventually_eq_scalar (I := I) α T hb
  rw [hev.fderiv_eq]
  have hscalarFn_at : MDifferentiableAt I 𝓘(ℝ) scalarFn b :=
    mdifferentiableAt_scalarFn_of_tensorSectionMDiffAt
      (I := I) (M := M) α T (b := b) hb hT_at
  exact (mfderiv_scalar_eq_chart_fderiv (I := I) α scalarFn (x := b)
    hb_src hb_tgt_int hscalarFn_at v).symm

end Connection
end Integral
end DifferentialGeometry

end
