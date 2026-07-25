import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.SlotCorrectionChartCompFormula
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartSmooth
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartLeviCivitaParallelCLMOpNorm
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.SlotUniformBound
import DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.SlotChartSourceContMDiff
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def slotInputConjCLM (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M)
    (i : Fin r) : E →L[ℝ] E :=
  if i = k then
    (chartTrivializationLinearMap (I := I) (M := M) α b).comp
      ((chartLeviCivitaParallelCLM (I := I) g α b B).comp
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b))
  else
    ContinuousLinearMap.id ℝ E

def slotOutputConjCLM (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M)
    (j : Fin s) : E →L[ℝ] E :=
  if j = l then
    (chartTrivializationLinearMap (I := I) (M := M) α b).comp
      ((chartLeviCivitaParallelCLM (I := I) g α b B).comp
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b))
  else
    ContinuousLinearMap.id ℝ E

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma slotInputConjCLM_self (g : SmoothRiemannianMetric I M) (r : ℕ)
    (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    slotInputConjCLM (I := I) g r α B k b k =
      (chartTrivializationLinearMap (I := I) (M := M) α b).comp
        ((chartLeviCivitaParallelCLM (I := I) g α b B).comp
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b)) := by
  unfold slotInputConjCLM
  simp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma slotInputConjCLM_other (g : SmoothRiemannianMetric I M) (r : ℕ)
    (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M)
    {i : Fin r} (h : i ≠ k) :
    slotInputConjCLM (I := I) g r α B k b i = ContinuousLinearMap.id ℝ E := by
  unfold slotInputConjCLM
  simp [h]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma slotOutputConjCLM_self (g : SmoothRiemannianMetric I M) (s : ℕ)
    (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    slotOutputConjCLM (I := I) g s α B l b l =
      (chartTrivializationLinearMap (I := I) (M := M) α b).comp
        ((chartLeviCivitaParallelCLM (I := I) g α b B).comp
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b)) := by
  unfold slotOutputConjCLM
  simp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma slotOutputConjCLM_other (g : SmoothRiemannianMetric I M) (s : ℕ)
    (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M)
    {j : Fin s} (h : j ≠ l) :
    slotOutputConjCLM (I := I) g s α B l b j = ContinuousLinearMap.id ℝ E := by
  unfold slotOutputConjCLM
  simp [h]

def inputSlotPrecompCLM (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel r ℝ E :=
  ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (E := fun _ : Fin r => E) (F := ℝ)
    (slotInputConjCLM (I := I) g r α B k b)

def outputSlotPostcompCLM (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E :=
  ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (E := fun _ : Fin s => E) (F := ℝ)
    (slotOutputConjCLM (I := I) g s α B l b)

def inputSlotChartKernel (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
      (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) :=
  (ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel r ℝ E) (Tensor0SModel s ℝ E)).flip
    (inputSlotPrecompCLM (I := I) g r α B k b)

def outputSlotChartKernel (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
      (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) :=
  (ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel s ℝ E) (Tensor0SModel s ℝ E))
    (outputSlotPostcompCLM (I := I) g s α B l b)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma inputSlotChartKernel_apply (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M)
    (S : Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) :
    inputSlotChartKernel (I := I) g r s α B k b S =
      S.comp (inputSlotPrecompCLM (I := I) g r α B k b) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma outputSlotChartKernel_apply (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M)
    (S : Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) :
    outputSlotChartKernel (I := I) g r s α B l b S =
      (outputSlotPostcompCLM (I := I) g s α B l b).comp S := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma slotInputConjCLM_compCLM_compCLM_chartJ
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (k : Fin r)
    (α' : Tensor0SModel r ℝ E) :
    (α'.compContinuousLinearMap
        (slotInputConjCLM (I := I) g r α B k b)).compContinuousLinearMap
      (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b) =
    α'.compContinuousLinearMap
      (fun i : Fin r => (chartTrivializationLinearMap (I := I) (M := M) α b).comp
        (tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b B) i)) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  have hfamily :
      (fun i : Fin r => (slotInputConjCLM (I := I) g r α B k b i).comp
          (chartTrivializationLinearMap (I := I) (M := M) α b)) =
      (fun i : Fin r => (chartTrivializationLinearMap (I := I) (M := M) α b).comp
          (tangentSlotCLM (I := I) r k
            (chartLeviCivitaParallelCLM (I := I) g α b B) i)) := by
    funext i
    by_cases hik : i = k
    · subst hik
      rw [slotInputConjCLM_self, tangentSlotCLM_self]
      refine ContinuousLinearMap.ext ?_
      intro x
      change chartTrivializationLinearMap (I := I) (M := M) α b
          ((chartLeviCivitaParallelCLM (I := I) g α b B)
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b
              (chartTrivializationLinearMap (I := I) (M := M) α b x))) =
        chartTrivializationLinearMap (I := I) (M := M) α b
          ((chartLeviCivitaParallelCLM (I := I) g α b B) x)
      rw [chartJinv_chartJ_self (I := I) (M := M) α hb_base]
    · rw [slotInputConjCLM_other (I := I) g r α B k b hik,
        tangentSlotCLM_other (I := I) r k _ hik]
      refine ContinuousLinearMap.ext ?_
      intro x
      change chartTrivializationLinearMap (I := I) (M := M) α b x = chartTrivializationLinearMap (I := I) (M := M) α b x
      rfl
  refine ContinuousMultilinearMap.ext ?_
  intro v
  have h_lhs_eq :
      (((α'.compContinuousLinearMap
            (slotInputConjCLM (I := I) g r α B k b)).compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)) v : ℝ) =
      α' (fun i : Fin r =>
        (slotInputConjCLM (I := I) g r α B k b i) (chartTrivializationLinearMap (I := I) (M := M) α b (v i))) := by
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [h_lhs_eq]
  have hfam_at_v : (fun i : Fin r =>
      (slotInputConjCLM (I := I) g r α B k b i) (chartTrivializationLinearMap (I := I) (M := M) α b (v i))) =
      (fun i : Fin r => (chartTrivializationLinearMap (I := I) (M := M) α b)
        ((tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b B) i) (v i))) := by
    funext i
    have hi := congrFun hfamily i
    have h_at_v := congrArg (fun (T : E →L[ℝ] E) => T (v i)) hi
    simp only [ContinuousLinearMap.comp_apply] at h_at_v
    exact h_at_v
  rw [hfam_at_v]
  exact (ContinuousMultilinearMap.compContinuousLinearMap_apply _ _ _).symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma slotOutputConjCLM_compose_chartJinv
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (l : Fin s)
    (m : Fin s → E) (j : Fin s) :
    chartTrivializationLinearMapSymm (I := I) (M := M) α b
        (slotOutputConjCLM (I := I) g s α B l b j (m j)) =
      tangentSlotCLM (I := I) s l
          (chartLeviCivitaParallelCLM (I := I) g α b B) j
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b (m j)) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  by_cases hjl : j = l
  · subst hjl
    rw [slotOutputConjCLM_self, tangentSlotCLM_self]
    change chartTrivializationLinearMapSymm (I := I) (M := M) α b
        (chartTrivializationLinearMap (I := I) (M := M) α b
          ((chartLeviCivitaParallelCLM (I := I) g α b B)
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b (m j)))) = _
    rw [chartJinv_chartJ_self (I := I) (M := M) α hb_base]
  · rw [slotOutputConjCLM_other (I := I) g s α B l b hjl,
      tangentSlotCLM_other (I := I) s l _ hjl]
    rw [ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartTensorRSInputSlotCorrection_chart_kernel_factorization
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (k : Fin r) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k) =
    (inputSlotChartKernel (I := I) g r s α B k b)
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (T b)) := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  refine ContinuousMultilinearMap.ext ?_
  intro w
  have hLHS_bridge :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
      r s α hb (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)
  have hRHS_bridge :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
      r s α hb (T b)
  have hLHS_eval :
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (chartTensorRSInputSlotCorrection (I := I) r s g α T B b k)
        α' w : ℝ) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (α'.compContinuousLinearMap
            (fun i : Fin r => (chartTrivializationLinearMap (I := I) (M := M) α b).comp
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b B) i))))
        (fun j : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b (w j)) := by
    rw [hLHS_bridge, chartRSTwistInv_apply]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have h_apply := chartTensorRSInputSlotCorrection_apply (I := I) r s g α T B b k
      (α'.compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))
      (fun j : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b (w j))
    have hsubst :
        (tensorSlotSubstCLM (I := I) r b
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B))
            (α'.compContinuousLinearMap
              (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))
          : Tensor0SSpace r I b) =
        α'.compContinuousLinearMap
          (fun i : Fin r => (chartTrivializationLinearMap (I := I) (M := M) α b).comp
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B) i)) := by
      refine ContinuousMultilinearMap.ext ?_
      intro v
      rw [tensorSlotSubstCLM_apply (I := I) r b
        (tangentSlotCLM (I := I) r k
          (chartLeviCivitaParallelCLM (I := I) g α b B))
        (α'.compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)) v]
      rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
      rfl
    rw [hsubst] at h_apply
    exact h_apply
  have hRHS_eval :
      ((inputSlotChartKernel (I := I) g r s α B k b)
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (T b)) α' w : ℝ) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (α'.compContinuousLinearMap
            (fun i : Fin r => (chartTrivializationLinearMap (I := I) (M := M) α b).comp
              (tangentSlotCLM (I := I) r k
                (chartLeviCivitaParallelCLM (I := I) g α b B) i))))
        (fun j : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b (w j)) := by
    rw [inputSlotChartKernel_apply, ContinuousLinearMap.comp_apply,
      hRHS_bridge, chartRSTwistInv_apply]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    have hkey :=
      slotInputConjCLM_compCLM_compCLM_chartJ (I := I) (M := M) g r α B hb k α'
    have h_unfold_precomp :
        ((inputSlotPrecompCLM (I := I) g r α B k b) α').compContinuousLinearMap
          (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b) =
        α'.compContinuousLinearMap
          (fun i : Fin r => (chartTrivializationLinearMap (I := I) (M := M) α b).comp
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b B) i)) := by
      unfold inputSlotPrecompCLM
      rw [ContinuousMultilinearMap.compContinuousLinearMapL_apply]
      exact hkey
    rw [h_unfold_precomp]
    rfl
  exact hLHS_eval.trans hRHS_eval.symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartTensorRSOutputSlotCorrection_chart_kernel_factorization
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (B : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (l : Fin s) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l) =
    (outputSlotChartKernel (I := I) g r s α B l b)
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (T b)) := by
  classical
  refine ContinuousLinearMap.ext ?_
  intro α'
  refine ContinuousMultilinearMap.ext ?_
  intro m
  have hLHS_bridge :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
      r s α hb (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)
  have hRHS_bridge :=
    triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
      r s α hb (T b)
  have hLHS_eval :
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (chartTensorRSOutputSlotCorrection (I := I) r s g α T B b l)
        α' m : ℝ) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (α'.compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)))
        (fun j : Fin s =>
          tangentSlotCLM (I := I) s l
            (chartLeviCivitaParallelCLM (I := I) g α b B) j
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b (m j))) := by
    rw [hLHS_bridge, chartRSTwistInv_apply]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    exact chartTensorRSOutputSlotCorrection_apply (I := I) r s g α T B b l
      (α'.compContinuousLinearMap
        (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b))
      (fun j : Fin s => chartTrivializationLinearMapSymm (I := I) (M := M) α b (m j))
  have hRHS_eval :
      ((outputSlotChartKernel (I := I) g r s α B l b)
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (T b)) α' m : ℝ) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (α'.compContinuousLinearMap
            (fun _ : Fin r => chartTrivializationLinearMap (I := I) (M := M) α b)))
        (fun j : Fin s =>
          tangentSlotCLM (I := I) s l
            (chartLeviCivitaParallelCLM (I := I) g α b B) j
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b (m j))) := by
    rw [outputSlotChartKernel_apply]
    rw [ContinuousLinearMap.comp_apply]
    rw [hRHS_bridge]
    unfold outputSlotPostcompCLM
    rw [ContinuousMultilinearMap.compContinuousLinearMapL_apply]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [chartRSTwistInv_apply]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext j
    exact slotOutputConjCLM_compose_chartJinv (I := I) (M := M) g s α B hb l m j
  exact hLHS_eval.trans hRHS_eval.symm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartLCConj_eq_christoffelCorrectionCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) :
    (chartTrivializationLinearMap (I := I) (M := M) α b).comp
        ((chartLeviCivitaParallelCLM (I := I) g α b X).comp
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b)) =
      christoffelCorrectionCLM (I := I) g α X b := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  refine ContinuousLinearMap.ext ?_
  intro w
  rw [ContinuousLinearMap.comp_apply]
  change chartTrivializationLinearMap (I := I) (M := M) α b
      ((chartLeviCivitaParallelCLM (I := I) g α b X)
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b w)) = _
  rw [chartLeviCivitaParallelCLM_apply (I := I) g α b X
    (chartTrivializationLinearMapSymm (I := I) (M := M) α b w)]
  change trivToE (I := I) α b
      (trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b (X b))
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b w))) = _
  rw [trivToE_trivFromE (I := I) α hb_base]
  exact christoffelCorrection_eq_christoffelCorrectionCLM (I := I) g α X hb_base w

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartLCConj_contMDiffOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun b : M =>
        (chartTrivializationLinearMap (I := I) (M := M) α b).comp
          ((chartLeviCivitaParallelCLM (I := I) g α b B.toFun).comp
            (chartTrivializationLinearMapSymm (I := I) (M := M) α b)))
      ((chartAt H α).source) := by
  classical
  have hB_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := fun y : M => TangentSpace I y) x (B.toFun x)) := B.contMDiff
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := hB_total.contMDiffOn
  have hχ_good : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (christoffelCorrectionCLM (I := I) g α B.toFun)
      (chartLeviCivitaGoodSet (I := I) α) :=
    christoffelCorrectionCLM_contMDiffOn (I := I) g α hB_on
  have h_good_eq_source :
      chartLeviCivitaGoodSet (I := I) α = (chartAt H α).source := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
      extChartAt_source_eq_chartAt_source (I := I)]
  have hχ : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
      (christoffelCorrectionCLM (I := I) g α B.toFun)
      ((chartAt H α).source) := by
    rw [← h_good_eq_source]; exact hχ_good
  refine hχ.congr ?_
  intro b hb
  exact chartLCConj_eq_christoffelCorrectionCLM (I := I) (M := M) g α B.toFun hb

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma goodSet_image_isOpen (α : M) :
    IsOpen ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
  chartLeviCivitaGoodSet_image_isOpen (I := I) α

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma goodSet_subset_chartSource (α : M) :
    chartLeviCivitaGoodSet (I := I) α ⊆ (chartAt H α).source := by
  intro b hb
  have h_eq :=
    chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
  rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)] at hb
  exact hb

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma extChartAt_mem_goodSet_image (α : M) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    extChartAt I α b ∈ (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
  ⟨b, hb, rfl⟩

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartLCConj_chart_pulled_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContDiffOn ℝ ∞
      (fun y : E =>
        (chartTrivializationLinearMap (I := I) (M := M) α ((extChartAt I α).symm y)).comp
          ((chartLeviCivitaParallelCLM (I := I) g α
              ((extChartAt I α).symm y) B.toFun).comp
            (chartTrivializationLinearMapSymm (I := I) (M := M) α ((extChartAt I α).symm y))))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hcm := chartLCConj_contMDiffOn_chartSource (I := I) (M := M) g α B
  set hgood_open : IsOpen (chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_isOpen (I := I) α
  intro y hy
  rcases hy with ⟨x, hxS, rfl⟩
  have hx_src : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hxS
  set F : M → E →L[ℝ] E := fun b : M =>
    (chartTrivializationLinearMap (I := I) (M := M) α b).comp
      ((chartLeviCivitaParallelCLM (I := I) g α b B.toFun).comp
        (chartTrivializationLinearMapSymm (I := I) (M := M) α b)) with hF_def
  have hF_at : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ F x := by
    have hopen_src : IsOpen (chartAt H α).source :=
      (chartAt H α).open_source
    exact hcm.contMDiffAt (hopen_src.mem_nhds hx_src)
  set φ := extChartAt I α
  have hxφ_src : x ∈ φ.source := by rw [extChartAt_source]; exact hx_src
  have hxφ_tgt : φ x ∈ φ.target := φ.map_source hxφ_src
  have hxφ_inv : φ.symm (φ x) = x := φ.left_inv hxφ_src
  have hsymm_on : ContMDiffOn 𝓘(ℝ, E) I (∞ : WithTop ℕ∞) φ.symm φ.target :=
    contMDiffOn_extChartAt_symm (I := I) (n := ∞) (x := α)
  have hsymm_at : ContMDiffWithinAt 𝓘(ℝ, E) I (∞ : WithTop ℕ∞)
      φ.symm φ.target (φ x) := hsymm_on (φ x) hxφ_tgt
  have hF_at' : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ F (φ.symm (φ x)) := by
    rw [hxφ_inv]; exact hF_at
  have hcomp_at : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
      (F ∘ φ.symm) φ.target (φ x) :=
    hF_at'.comp_contMDiffWithinAt (φ x) hsymm_at
  rw [contMDiffWithinAt_iff_contDiffWithinAt] at hcomp_at
  refine hcomp_at.mono ?_
  intro z hz
  rcases hz with ⟨x', hx'_good, rfl⟩
  exact interior_subset
    (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx'_good)

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartLCConj_chart_pulled_contDiffAt
    (g : SmoothRiemannianMetric I M) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞
      (fun y : E =>
        (chartTrivializationLinearMap (I := I) (M := M) α ((extChartAt I α).symm y)).comp
          ((chartLeviCivitaParallelCLM (I := I) g α
              ((extChartAt I α).symm y) B.toFun).comp
            (chartTrivializationLinearMapSymm (I := I) (M := M) α ((extChartAt I α).symm y))))
      (extChartAt I α b) := by
  classical
  have hOpen := goodSet_image_isOpen (I := I) (M := M) α
  have hmem : extChartAt I α b ∈
      (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    extChartAt_mem_goodSet_image (I := I) (M := M) α hb
  exact (chartLCConj_chart_pulled_contDiffOn (I := I) (M := M) g α B).contDiffAt
    (hOpen.mem_nhds hmem)

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma slotInputConjCLM_chart_pulled_contDiffAt
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (i : Fin r) :
    ContDiffAt ℝ ∞
      (fun y : E =>
        slotInputConjCLM (I := I) g r α B.toFun k
          ((extChartAt I α).symm y) i)
      (extChartAt I α b) := by
  classical
  by_cases hik : i = k
  · subst hik
    have heq : (fun y : E =>
        slotInputConjCLM (I := I) g r α B.toFun i ((extChartAt I α).symm y) i) =
      (fun y : E =>
        (chartTrivializationLinearMap (I := I) (M := M) α ((extChartAt I α).symm y)).comp
          ((chartLeviCivitaParallelCLM (I := I) g α
              ((extChartAt I α).symm y) B.toFun).comp
            (chartTrivializationLinearMapSymm (I := I) (M := M) α ((extChartAt I α).symm y)))) := by
      funext y
      exact slotInputConjCLM_self (I := I) g r α B.toFun i ((extChartAt I α).symm y)
    rw [heq]
    exact chartLCConj_chart_pulled_contDiffAt (I := I) (M := M) g α B hb
  · have heq : (fun y : E =>
        slotInputConjCLM (I := I) g r α B.toFun k ((extChartAt I α).symm y) i) =
      (fun _ : E => ContinuousLinearMap.id ℝ E) := by
      funext y
      exact slotInputConjCLM_other (I := I) g r α B.toFun k _ hik
    rw [heq]
    exact contDiffAt_const

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma slotOutputConjCLM_chart_pulled_contDiffAt
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) (j : Fin s) :
    ContDiffAt ℝ ∞
      (fun y : E =>
        slotOutputConjCLM (I := I) g s α B.toFun l
          ((extChartAt I α).symm y) j)
      (extChartAt I α b) := by
  classical
  by_cases hjl : j = l
  · subst hjl
    have heq : (fun y : E =>
        slotOutputConjCLM (I := I) g s α B.toFun j ((extChartAt I α).symm y) j) =
      (fun y : E =>
        (chartTrivializationLinearMap (I := I) (M := M) α ((extChartAt I α).symm y)).comp
          ((chartLeviCivitaParallelCLM (I := I) g α
              ((extChartAt I α).symm y) B.toFun).comp
            (chartTrivializationLinearMapSymm (I := I) (M := M) α ((extChartAt I α).symm y)))) := by
      funext y
      exact slotOutputConjCLM_self (I := I) g s α B.toFun j ((extChartAt I α).symm y)
    rw [heq]
    exact chartLCConj_chart_pulled_contDiffAt (I := I) (M := M) g α B hb
  · have heq : (fun y : E =>
        slotOutputConjCLM (I := I) g s α B.toFun l ((extChartAt I α).symm y) j) =
      (fun _ : E => ContinuousLinearMap.id ℝ E) := by
      funext y
      exact slotOutputConjCLM_other (I := I) g s α B.toFun l _ hjl
    rw [heq]
    exact contDiffAt_const

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma inputSlotPrecompCLM_chart_pulled_contDiffAt
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞
      (fun y : E =>
        inputSlotPrecompCLM (I := I) g r α B.toFun k
          ((extChartAt I α).symm y))
      (extChartAt I α b) := by
  classical
  set hmulti : ContinuousMultilinearMap ℝ (fun _ : Fin r => E →L[ℝ] E)
      ((ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      ℝ (fun _ : Fin r => E) (fun _ : Fin r => E) ℝ with hmulti_def
  have hpi : ContDiffAt ℝ ∞
      (fun y : E =>
        fun i : Fin r => slotInputConjCLM (I := I) g r α B.toFun k
          ((extChartAt I α).symm y) i)
      (extChartAt I α b) := by
    refine contDiffAt_pi.mpr ?_
    intro i
    exact slotInputConjCLM_chart_pulled_contDiffAt (I := I) (M := M)
      g r α B k hb i
  have hcomposed :=
    (hmulti.contDiff (𝕜 := ℝ)).contDiffAt.comp (x := extChartAt I α b) hpi
  have h_eval :
      ∀ y : E,
        (hmulti
            (fun i : Fin r => slotInputConjCLM (I := I) g r α B.toFun k
              ((extChartAt I α).symm y) i)
          : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →L[ℝ]
              ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ) =
        inputSlotPrecompCLM (I := I) g r α B.toFun k
          ((extChartAt I α).symm y) := by
    intro y
    refine ContinuousLinearMap.ext ?_
    intro w
    rfl
  refine hcomposed.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  exact h_eval y

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma outputSlotPostcompCLM_chart_pulled_contDiffAt
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞
      (fun y : E =>
        outputSlotPostcompCLM (I := I) g s α B.toFun l
          ((extChartAt I α).symm y))
      (extChartAt I α b) := by
  classical
  set hmulti : ContinuousMultilinearMap ℝ (fun _ : Fin s => E →L[ℝ] E)
      ((ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      ℝ (fun _ : Fin s => E) (fun _ : Fin s => E) ℝ with hmulti_def
  have hpi : ContDiffAt ℝ ∞
      (fun y : E =>
        fun j : Fin s => slotOutputConjCLM (I := I) g s α B.toFun l
          ((extChartAt I α).symm y) j)
      (extChartAt I α b) := by
    refine contDiffAt_pi.mpr ?_
    intro j
    exact slotOutputConjCLM_chart_pulled_contDiffAt (I := I) (M := M)
      g s α B l hb j
  have hcomposed :=
    (hmulti.contDiff (𝕜 := ℝ)).contDiffAt.comp (x := extChartAt I α b) hpi
  have h_eval :
      ∀ y : E,
        (hmulti
            (fun j : Fin s => slotOutputConjCLM (I := I) g s α B.toFun l
              ((extChartAt I α).symm y) j)
          : ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ →L[ℝ]
              ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) =
        outputSlotPostcompCLM (I := I) g s α B.toFun l
          ((extChartAt I α).symm y) := by
    intro y
    refine ContinuousLinearMap.ext ?_
    intro w
    rfl
  refine hcomposed.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  exact h_eval y

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem inputSlotChartKernel_contDiffAt_chart_pulled
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (k : Fin r) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
  classical
  have h_precomp := inputSlotPrecompCLM_chart_pulled_contDiffAt
    (I := I) (M := M) g r α B k hb
  set L : (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel r ℝ E) →L[ℝ]
      ((Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
        (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)) :=
    (ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel r ℝ E) (Tensor0SModel s ℝ E)).flip with hL_def
  have hL_smooth : ContDiff ℝ ∞ (L : _ → _) := L.contDiff
  have hcomposed := hL_smooth.contDiffAt.comp (x := extChartAt I α b) h_precomp
  refine hcomposed.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  rfl

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem outputSlotChartKernel_contDiffAt_chart_pulled
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (l : Fin s) {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ContDiffAt ℝ ∞
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
  classical
  have h_postcomp := outputSlotPostcompCLM_chart_pulled_contDiffAt
    (I := I) (M := M) g s α B l hb
  set L : (Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
      ((Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
        (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)) :=
    ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel s ℝ E) (Tensor0SModel s ℝ E) with hL_def
  have hL_smooth : ContDiff ℝ ∞ (L : _ → _) := L.contDiff
  have hcomposed := hL_smooth.contDiffAt.comp (x := extChartAt I α b) h_postcomp
  refine hcomposed.congr_of_eventuallyEq ?_
  refine Filter.Eventually.of_forall ?_
  intro y
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma chartLCConj_opNorm_le (g : SmoothRiemannianMetric I M) (α b : M)
    (X : Π b' : M, TangentSpace I b') :
    ‖(chartTrivializationLinearMap (I := I) (M := M) α b).comp
        ((chartLeviCivitaParallelCLM (I := I) g α b X).comp
          (chartTrivializationLinearMapSymm (I := I) (M := M) α b))‖ ≤
      ‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
        (‖chartLeviCivitaParallelCLM (I := I) g α b X‖ *
          ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖) := by
  refine ContinuousLinearMap.opNorm_comp_le _ _ |>.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact ContinuousLinearMap.opNorm_comp_le _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma slotInputConjCLM_opNorm_le (g : SmoothRiemannianMetric I M)
    (r : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M)
    (i : Fin r) :
    ‖slotInputConjCLM (I := I) g r α B k b i‖ ≤
      max 1
        (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖)) := by
  classical
  by_cases hik : i = k
  · subst hik
    rw [slotInputConjCLM_self]
    refine le_trans (chartLCConj_opNorm_le (I := I) (M := M) g α b B) ?_
    exact le_max_right _ _
  · rw [slotInputConjCLM_other (I := I) g r α B k b hik]
    refine ContinuousLinearMap.norm_id_le.trans ?_
    exact le_max_left _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma slotOutputConjCLM_opNorm_le (g : SmoothRiemannianMetric I M)
    (s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M)
    (j : Fin s) :
    ‖slotOutputConjCLM (I := I) g s α B l b j‖ ≤
      max 1
        (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖)) := by
  classical
  by_cases hjl : j = l
  · subst hjl
    rw [slotOutputConjCLM_self]
    refine le_trans (chartLCConj_opNorm_le (I := I) (M := M) g α b B) ?_
    exact le_max_right _ _
  · rw [slotOutputConjCLM_other (I := I) g s α B l b hjl]
    refine ContinuousLinearMap.norm_id_le.trans ?_
    exact le_max_left _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma slotInputConjCLM_prod_opNorm_le (g : SmoothRiemannianMetric I M)
    (r : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    (∏ i : Fin r, ‖slotInputConjCLM (I := I) g r α B k b i‖) ≤
      (max 1
        (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖))) ^ r := by
  classical
  set M_b : ℝ := max 1
    (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
      (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
        ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖)) with hM_def
  have h_pow : M_b ^ r = ∏ _i : Fin r, M_b := by
    rw [Finset.prod_const]; simp
  rw [h_pow]
  refine Finset.prod_le_prod ?_ ?_
  · intro i _; exact norm_nonneg _
  · intro i _; exact slotInputConjCLM_opNorm_le (I := I) (M := M) g r α B k b i

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma slotOutputConjCLM_prod_opNorm_le (g : SmoothRiemannianMetric I M)
    (s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    (∏ j : Fin s, ‖slotOutputConjCLM (I := I) g s α B l b j‖) ≤
      (max 1
        (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖))) ^ s := by
  classical
  set M_b : ℝ := max 1
    (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
      (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
        ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖)) with hM_def
  have h_pow : M_b ^ s = ∏ _j : Fin s, M_b := by
    rw [Finset.prod_const]; simp
  rw [h_pow]
  refine Finset.prod_le_prod ?_ ?_
  · intro j _; exact norm_nonneg _
  · intro j _; exact slotOutputConjCLM_opNorm_le (I := I) (M := M) g s α B l b j

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma inputSlotPrecompCLM_opNorm_le (g : SmoothRiemannianMetric I M)
    (r : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    ‖inputSlotPrecompCLM (I := I) g r α B k b‖ ≤
      (max 1
        (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖))) ^ r := by
  classical
  unfold inputSlotPrecompCLM
  refine le_trans
    (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
      (𝕜 := ℝ) (E := fun _ : Fin r => E) ℝ _) ?_
  exact slotInputConjCLM_prod_opNorm_le (I := I) (M := M) g r α B k b

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma outputSlotPostcompCLM_opNorm_le (g : SmoothRiemannianMetric I M)
    (s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    ‖outputSlotPostcompCLM (I := I) g s α B l b‖ ≤
      (max 1
        (‖chartTrivializationLinearMap (I := I) (M := M) α b‖ *
          (‖chartLeviCivitaParallelCLM (I := I) g α b B‖ *
            ‖chartTrivializationLinearMapSymm (I := I) (M := M) α b‖))) ^ s := by
  classical
  unfold outputSlotPostcompCLM
  refine le_trans
    (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
      (𝕜 := ℝ) (E := fun _ : Fin s => E) ℝ _) ?_
  exact slotOutputConjCLM_prod_opNorm_le (I := I) (M := M) g s α B l b

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma inputSlotChartKernel_opNorm_le (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (k : Fin r) (b : M) :
    ‖inputSlotChartKernel (I := I) g r s α B k b‖ ≤
      ‖inputSlotPrecompCLM (I := I) g r α B k b‖ := by
  classical
  unfold inputSlotChartKernel
  refine le_trans ((ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
    (Tensor0SModel r ℝ E) (Tensor0SModel s ℝ E)).flip.le_opNorm _) ?_
  rw [ContinuousLinearMap.opNorm_flip]
  have h_le := ContinuousLinearMap.norm_compL_le (𝕜 := ℝ)
    (E := Tensor0SModel r ℝ E) (Fₗ := Tensor0SModel r ℝ E)
    (Gₗ := Tensor0SModel s ℝ E)
  have h_nn : 0 ≤ ‖inputSlotPrecompCLM (I := I) g r α B k b‖ := norm_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_right h_le h_nn) ?_
  rw [one_mul]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma outputSlotChartKernel_opNorm_le (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α : M) (B : Π b' : M, TangentSpace I b') (l : Fin s) (b : M) :
    ‖outputSlotChartKernel (I := I) g r s α B l b‖ ≤
      ‖outputSlotPostcompCLM (I := I) g s α B l b‖ := by
  classical
  unfold outputSlotChartKernel
  refine le_trans ((ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
    (Tensor0SModel s ℝ E) (Tensor0SModel s ℝ E)).le_opNorm _) ?_
  have h_le := ContinuousLinearMap.norm_compL_le (𝕜 := ℝ)
    (E := Tensor0SModel r ℝ E) (Fₗ := Tensor0SModel s ℝ E)
    (Gₗ := Tensor0SModel s ℝ E)
  have h_nn : 0 ≤ ‖outputSlotPostcompCLM (I := I) g s α B l b‖ := norm_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_right h_le h_nn) ?_
  rw [one_mul]

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem inputSlotChartKernel_chart_pulled_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ContDiffOn ℝ ∞
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  set L : (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel r ℝ E) →L[ℝ]
      ((Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
        (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)) :=
    (ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel r ℝ E) (Tensor0SModel s ℝ E)).flip with hL_def
  have hL_smooth : ContDiff ℝ ∞ (L : _ → _) := L.contDiff
  intro y hy
  obtain ⟨b, hb_good, hyb⟩ := hy
  subst hyb
  have h_precomp_at := inputSlotPrecompCLM_chart_pulled_contDiffAt
    (I := I) (M := M) g r α B k hb_good
  have hcomposed := hL_smooth.contDiffAt.comp (x := extChartAt I α b) h_precomp_at
  have h_at : ContDiffAt ℝ ∞
      (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
    refine hcomposed.congr_of_eventuallyEq ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    rfl
  exact h_at.contDiffWithinAt

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem outputSlotChartKernel_chart_pulled_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ContDiffOn ℝ ∞
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  set L : (Tensor0SModel s ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
      ((Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) →L[ℝ]
        (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E)) :=
    ContinuousLinearMap.compL ℝ (Tensor0SModel r ℝ E)
      (Tensor0SModel s ℝ E) (Tensor0SModel s ℝ E) with hL_def
  have hL_smooth : ContDiff ℝ ∞ (L : _ → _) := L.contDiff
  intro y hy
  obtain ⟨b, hb_good, hyb⟩ := hy
  subst hyb
  have h_postcomp_at := outputSlotPostcompCLM_chart_pulled_contDiffAt
    (I := I) (M := M) g s α B l hb_good
  have hcomposed := hL_smooth.contDiffAt.comp (x := extChartAt I α b) h_postcomp_at
  have h_at : ContDiffAt ℝ ∞
      (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                      ((extChartAt I α).symm y))
      (extChartAt I α b) := by
    refine hcomposed.congr_of_eventuallyEq ?_
    refine Filter.Eventually.of_forall ?_
    intro y
    rfl
  exact h_at.contDiffWithinAt

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma inputSlotChartKernel_fderiv_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ContinuousOn
      (fun y : E => ‖fderiv ℝ
        (fun y' : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y')) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hcd := inputSlotChartKernel_chart_pulled_contDiffOn (I := I) (M := M)
    g r s α B k
  have hOpen := goodSet_image_isOpen (I := I) (M := M) α
  have hfd_cd : ContDiffOn ℝ ∞
      (fderiv ℝ (fun y' : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y')))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
    have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact hcd.fderiv_of_isOpen hOpen h_le
  exact continuous_norm.comp_continuousOn hfd_cd.continuousOn

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma outputSlotChartKernel_fderiv_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ContinuousOn
      (fun y : E => ‖fderiv ℝ
        (fun y' : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y')) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hcd := outputSlotChartKernel_chart_pulled_contDiffOn (I := I) (M := M)
    g r s α B l
  have hOpen := goodSet_image_isOpen (I := I) (M := M) α
  have hfd_cd : ContDiffOn ℝ ∞
      (fderiv ℝ (fun y' : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y')))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
    have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact hcd.fderiv_of_isOpen hOpen h_le
  exact continuous_norm.comp_continuousOn hfd_cd.continuousOn

omit [NeZero (Module.finrank ℝ E)] in
theorem inputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (k : Fin r) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖fderiv ℝ
            (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                            ((extChartAt I α).symm y))
            (extChartAt I α b)‖ ≤ K := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hcont := inputSlotChartKernel_fderiv_continuousOn (I := I) (M := M)
    g r s α B k
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α := by
    intro b hb
    have h_eq :=
      chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
    rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
    exact hK_sub hb
  have hmaps : Set.MapsTo (extChartAt I α) K_set
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have hcont_M : ContinuousOn (fun b : M =>
      ‖fderiv ℝ
        (fun y : E => inputSlotChartKernel (I := I) g r s α B.toFun k
                        ((extChartAt I α).symm y)) (extChartAt I α b)‖) K_set :=
    hcont.comp hφ_cont hmaps
  obtain ⟨C, hC_mem⟩ := hK_compact.bddAbove_image hcont_M
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  have hb_K : b ∈ K_set := hb.1
  have h := hC_mem ⟨b, hb_K, rfl⟩
  exact le_trans h (le_max_left _ _)

omit [NeZero (Module.finrank ℝ E)] in
theorem outputSlotChartKernel_fderiv_opNorm_uniform_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (l : Fin s) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
          chartLeviCivitaGoodSet (I := I) α →
        ‖fderiv ℝ
            (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                            ((extChartAt I α).symm y))
            (extChartAt I α b)‖ ≤ K := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hcont := outputSlotChartKernel_fderiv_continuousOn (I := I) (M := M)
    g r s α B l
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α := by
    intro b hb
    have h_eq :=
      chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α
    rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
    exact hK_sub hb
  have hmaps : Set.MapsTo (extChartAt I α) K_set
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have hcont_M : ContinuousOn (fun b : M =>
      ‖fderiv ℝ
        (fun y : E => outputSlotChartKernel (I := I) g r s α B.toFun l
                        ((extChartAt I α).symm y)) (extChartAt I α b)‖) K_set :=
    hcont.comp hφ_cont hmaps
  obtain ⟨C, hC_mem⟩ := hK_compact.bddAbove_image hcont_M
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  have hb_K : b ∈ K_set := hb.1
  have h := hC_mem ⟨b, hb_K, rfl⟩
  exact le_trans h (le_max_left _ _)

end Connection
end Integral
end DifferentialGeometry

end
