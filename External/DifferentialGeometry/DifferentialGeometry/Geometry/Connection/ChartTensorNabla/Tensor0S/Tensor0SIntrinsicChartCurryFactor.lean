import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SChartChristoffel
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0SPartialEval
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SCovariantDerivative
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval


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
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

noncomputable def curryLeftEvalCLM (s : ℕ) (w : E) :
    Tensor0SModel (s + 1) ℝ E →L[ℝ] Tensor0SModel s ℝ E :=
  (ContinuousLinearMap.apply ℝ (Tensor0SModel s ℝ E) w).comp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (s + 1) => E)
        ℝ).toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace E] in
@[simp] lemma curryLeftEvalCLM_apply (s : ℕ) (w : E)
    (F : Tensor0SModel (s + 1) ℝ E) (m : Fin s → E) :
    (curryLeftEvalCLM (E := E) s w F) m = F (Fin.cons w m) := by
  classical
  unfold curryLeftEvalCLM
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    continuousMultilinearCurryLeftEquiv_apply]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SChartE_section_repr_apply_tuple {n : ℕ} (α : M)
    (T : Π b : M, Tensor0SSpace n I b) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v : Fin n → E) :
    (tensor0SChartE_section_repr (I := I) n α T b) v =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin n => TangentSpace I b) ℝ from T b)
        (fun i => trivFromE (I := I) α b (v i)) := by
  classical
  have hbase : b ∈ (trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).baseSet := by
    change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
    exact hb
  have hcoe := (trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).coe_linearMapAt_of_mem (R := ℝ) hbase
  unfold tensor0SChartE_section_repr
  change ((trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).linearMapAt ℝ b (T b)) v = _
  rw [show ((trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).linearMapAt ℝ b) (T b) =
        ((trivializationAt (Tensor0SModel n ℝ E)
          (fun y : M => Tensor0SSpace n I y) α) ⟨b, T b⟩).2 from
      congrFun hcoe (T b)]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SBundle_symmL_apply_eq_compContinuousLinearMap {n : ℕ}
    (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (D : Tensor0SModel n ℝ E) :
    letI _h_top : TopologicalSpace (TotalSpace (Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SSpace n I y)) :=
      tensor0SBundle_topology n
    ((trivializationAt (Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SSpace n I y) α).symmL ℝ b D :
        Tensor0SSpace n I b) =
      (D.compContinuousLinearMap (fun _ : Fin n => trivToE (I := I) α b) :
        ContinuousMultilinearMap ℝ
          (fun _ : Fin n => TangentSpace I b) ℝ) := by
  letI _h_top : TopologicalSpace (TotalSpace (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y)) :=
    tensor0SBundle_topology n
  have h := _root_.Pretrivialization.continuousMultilinearMap_symm_apply'
    (𝕜 := ℝ) (s := n) (F := E) (E := (TangentSpace I : M → Type _))
    (e := trivializationAt E (TangentSpace I) α) (b := b) hb D
  change (trivializationAt (Tensor0SModel n ℝ E)
      (fun y : M => Tensor0SSpace n I y) α).symm b D = _
  rw [show (trivializationAt (Tensor0SModel n ℝ E)
        (fun y : M => Tensor0SSpace n I y) α).symm b D =
          ((Pretrivialization.continuousMultilinearMap (𝕜 := ℝ) (s := n)
            (F := E) (E := (TangentSpace I : M → Type _))
            (trivializationAt E (TangentSpace I) α)).symm b D) from rfl]
  exact h

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SChartE_section_repr_cons_eq_partialEval (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace (s + 1) I b) {b : M} (v : TangentSpace I b)
    {b' : M} (hb' : b' ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (m : Fin s → E) :
    (tensor0SChartE_section_repr (I := I) (s + 1) α T b')
        (Fin.cons (trivToE (I := I) α b v) m) =
      (tensor0SChartE_section_repr (I := I) s α
        (Tensor0SPartialEval.tensor0SPartialEval I M T
          (chartParallelExtend (I := I) α b v)) b') m := by
  classical
  rw [tensor0SChartE_section_repr_apply_tuple (I := I) (n := s + 1) α T hb']
  rw [tensor0SChartE_section_repr_apply_tuple (I := I) (n := s) α _ hb']
  have hRHS_eval :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b') ℝ from
          Tensor0SPartialEval.tensor0SPartialEval I M T
            (chartParallelExtend (I := I) α b v) b')
          (fun i => trivFromE (I := I) α b' (m i)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b') ℝ from T b')
        (Fin.cons (chartParallelExtend (I := I) α b v b')
          (fun i => trivFromE (I := I) α b' (m i))) := by
    change (show ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I b') ℝ from
            tensor0S_curry (I := I) (M := M) s b' (T b')
              (chartParallelExtend (I := I) α b v b'))
            (fun i => trivFromE (I := I) α b' (m i)) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b') ℝ from T b')
        (Fin.cons (chartParallelExtend (I := I) α b v b')
          (fun i => trivFromE (I := I) α b' (m i)))
    exact TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := T b') (v0 := chartParallelExtend (I := I) α b v b')
      (vs := fun i => trivFromE (I := I) α b' (m i))
  rw [hRHS_eval]
  congr 1
  funext j
  refine Fin.cases ?_ ?_ j
  · simp only [Fin.cons_zero]; rfl
  · intro k; simp only [Fin.cons_succ]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SChartE_section_repr_partialEval_eq_curryLeftEval (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace (s + 1) I b) {b : M} (v : TangentSpace I b)
    {b' : M} (hb' : b' ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    tensor0SChartE_section_repr (I := I) s α
        (Tensor0SPartialEval.tensor0SPartialEval I M T
          (chartParallelExtend (I := I) α b v)) b' =
      curryLeftEvalCLM (E := E) s (trivToE (I := I) α b v)
        (tensor0SChartE_section_repr (I := I) (s + 1) α T b') := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  rw [curryLeftEvalCLM_apply]
  exact (tensor0SChartE_section_repr_cons_eq_partialEval (I := I) (M := M) s α T
    (b := b) v (b' := b') hb' m).symm

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem partialEval_chartPullback_eventually_eq_curryLeftEval_chartPullback
    (s : ℕ) (α : M) (T : Π b : M, Tensor0SSpace (s + 1) I b)
    {b : M} (v : TangentSpace I b)
    (hb_src : b ∈ (extChartAt I α).source)
    (hb_tgt : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (tensor0SChartE_section_repr (I := I) s α
        (Tensor0SPartialEval.tensor0SPartialEval I M T
          (chartParallelExtend (I := I) α b v)) ∘
        (extChartAt I α).symm) =ᶠ[𝓝 (extChartAt I α b)]
      (fun y : E =>
        curryLeftEvalCLM (E := E) s (trivToE (I := I) α b v)
          ((tensor0SChartE_section_repr (I := I) (s + 1) α T ∘
            (extChartAt I α).symm) y)) := by
  classical
  set φ := extChartAt I α
  have hU_int : interior (φ.target : Set E) ∈ 𝓝 (φ b) :=
    isOpen_interior.mem_nhds hb_tgt
  have hBase_open : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  have hb_inv : φ.symm (φ b) = b := φ.left_inv hb_src
  have hcont_symm : ContinuousAt φ.symm (φ b) :=
    continuousAt_extChartAt_symm' (I := I) (x := α) (x' := b) hb_src
  have hBase_pre : φ.symm ⁻¹' (trivializationAt E (TangentSpace I) α).baseSet ∈ 𝓝 (φ b) := by
    have hmem : (φ.symm (φ b)) ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [hb_inv]; exact hb_base
    exact hcont_symm.preimage_mem_nhds (hBase_open.mem_nhds hmem)
  filter_upwards [Filter.inter_mem hU_int hBase_pre] with y hy
  obtain ⟨_, hyBase⟩ := hy
  exact tensor0SChartE_section_repr_partialEval_eq_curryLeftEval
    (I := I) (M := M) s α T (b := b) v (b' := φ.symm y) hyBase

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem fderiv_partialEval_chartPullback_eq_comp_curryLeftEval (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    {b : M} (v : TangentSpace I b)
    (hb_src : b ∈ (extChartAt I α).source)
    (hb_tgt : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E))
    (hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hT : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) (s + 1) α T ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    fderiv ℝ
        (tensor0SChartE_section_repr (I := I) s α
            (Tensor0SPartialEval.tensor0SPartialEval I M T
              (chartParallelExtend (I := I) α b v)) ∘
          (extChartAt I α).symm)
        (extChartAt I α b) =
      (curryLeftEvalCLM (E := E) s (trivToE (I := I) α b v)).comp
        (fderiv ℝ
          (tensor0SChartE_section_repr (I := I) (s + 1) α T ∘
            (extChartAt I α).symm)
          (extChartAt I α b)) := by
  classical
  have heq := partialEval_chartPullback_eventually_eq_curryLeftEval_chartPullback
    (I := I) (M := M) s α T (b := b) v hb_src hb_tgt hb_base
  rw [Filter.EventuallyEq.fderiv_eq heq]
  exact (((curryLeftEvalCLM (E := E) s (trivToE (I := I) α b v)).hasFDerivAt
      (x := (tensor0SChartE_section_repr (I := I) (s + 1) α T ∘
        (extChartAt I α).symm) (extChartAt I α b))).comp
    (extChartAt I α b) hT.hasFDerivAt).fderiv

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor0SIntrinsicChartCLM_factor_via_partialEval
    (s : ℕ) (α : M) (T : Π b : M, Tensor0SSpace (s + 1) I b)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b)
    (hT : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) (s + 1) α T ∘ (extChartAt I α).symm)
      (extChartAt I α b))
    (X : Π b' : M, TangentSpace I b')
    (m : Fin s → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
      tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b))
        (Fin.cons (chartParallelExtend (I := I) α b v b) m) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        tensor0SIntrinsicChartCLM (I := I) s α
          (Tensor0SPartialEval.tensor0SPartialEval I M T
            (chartParallelExtend (I := I) α b v))
          b (X b)) m := by
  classical
  letI _h_top_succ : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun y : M => Tensor0SSpace (s + 1) I y)) :=
    tensor0SBundle_topology (s + 1)
  letI _h_top_s : TopologicalSpace (TotalSpace (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y)) :=
    tensor0SBundle_topology s
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hb_tgt : extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  set w : E := trivToE (I := I) α b (X b) with hw_def
  set mE : Fin s → E := fun i => trivToE (I := I) α b (m i) with hmt_def
  have hLHS_unfold :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
        tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b))
        (Fin.cons (chartParallelExtend (I := I) α b v b) m) =
      (fderiv ℝ
        (tensor0SChartE_section_repr (I := I) (s + 1) α T ∘ (extChartAt I α).symm)
        (extChartAt I α b) w)
        (Fin.cons (trivToE (I := I) α b v) mE) := by
    rw [tensor0SIntrinsicChartCLM_apply (I := I) (s + 1) α T b (X b)]
    show (show ContinuousMultilinearMap ℝ
        (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
        tensor0SChartFiberFromModel (I := I) (s + 1) α b
          (fderiv ℝ
            (tensor0SChartE_section_repr (I := I) (s + 1) α T ∘ (extChartAt I α).symm)
            (extChartAt I α b) (trivToE (I := I) α b (X b))))
        (Fin.cons (chartParallelExtend (I := I) α b v b) m) = _
    unfold tensor0SChartFiberFromModel
    set D := fderiv ℝ
        (tensor0SChartE_section_repr (I := I) (s + 1) α T ∘ (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (X b))
    rw [tensor0SBundle_symmL_apply_eq_compContinuousLinearMap
      (I := I) (M := M) (n := s + 1) α hb_base D]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext j
    refine Fin.cases ?_ ?_ j
    · simp only [Fin.cons_zero]
      change trivToE (I := I) α b
          (trivFromE (I := I) α b (trivToE (I := I) α b v)) = trivToE (I := I) α b v
      exact trivToE_trivFromE (I := I) α hb_base _
    · intro k
      simp only [Fin.cons_succ]
      rfl
  rw [hLHS_unfold]
  have hRHS_unfold :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        tensor0SIntrinsicChartCLM (I := I) s α
          (Tensor0SPartialEval.tensor0SPartialEval I M T
            (chartParallelExtend (I := I) α b v))
          b (X b)) m =
      (fderiv ℝ
        (tensor0SChartE_section_repr (I := I) s α
            (Tensor0SPartialEval.tensor0SPartialEval I M T
              (chartParallelExtend (I := I) α b v)) ∘
          (extChartAt I α).symm)
        (extChartAt I α b) w) mE := by
    rw [tensor0SIntrinsicChartCLM_apply (I := I) s α _ b (X b)]
    show (show ContinuousMultilinearMap ℝ
        (fun _ : Fin s => TangentSpace I b) ℝ from
        tensor0SChartFiberFromModel (I := I) s α b
          (fderiv ℝ
            (tensor0SChartE_section_repr (I := I) s α _ ∘ (extChartAt I α).symm)
            (extChartAt I α b) (trivToE (I := I) α b (X b)))) m = _
    unfold tensor0SChartFiberFromModel
    set D' := fderiv ℝ
        (tensor0SChartE_section_repr (I := I) s α
          (Tensor0SPartialEval.tensor0SPartialEval I M T
            (chartParallelExtend (I := I) α b v)) ∘ (extChartAt I α).symm)
        (extChartAt I α b) (trivToE (I := I) α b (X b))
    rw [tensor0SBundle_symmL_apply_eq_compContinuousLinearMap
      (I := I) (M := M) (n := s) α hb_base D']
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hRHS_unfold]
  have hfderivEq := fderiv_partialEval_chartPullback_eq_comp_curryLeftEval
    (I := I) (M := M) s α T (b := b) v hb_src hb_tgt hb_base hT
  have hfderiv_at_w : fderiv ℝ
        (tensor0SChartE_section_repr (I := I) s α
            (Tensor0SPartialEval.tensor0SPartialEval I M T
              (chartParallelExtend (I := I) α b v)) ∘
          (extChartAt I α).symm)
        (extChartAt I α b) w =
      curryLeftEvalCLM (E := E) s (trivToE (I := I) α b v)
        (fderiv ℝ
          (tensor0SChartE_section_repr (I := I) (s + 1) α T ∘
            (extChartAt I α).symm)
          (extChartAt I α b) w) := by
    have := congrArg (fun L : E →L[ℝ] Tensor0SModel s ℝ E => L w) hfderivEq
    simpa [ContinuousLinearMap.comp_apply] using this
  rw [hfderiv_at_w, curryLeftEvalCLM_apply]

end Connection
end Integral
end DifferentialGeometry

end
