import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SIntrinsicChartRank0
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SSlotShift
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SIntrinsicChartCurryFactor
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartLeviCivitaParallelExtend
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs


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
open Tensor0SNabla
open Tensor0SPartialEval

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
private lemma tensor0S_curry_symm_apply_cons (s : ℕ) {b : M}
    (Φ : TangentSpace I b →L[ℝ] Tensor0SSpace s I b)
    (v : TangentSpace I b) (m : Fin s → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
      (tensor0S_curry (I := I) (M := M) s b).symm Φ)
        (Fin.cons v m) =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from Φ v) m := by
  classical
  set P : Tensor0SSpace (s + 1) I b :=
    (tensor0S_curry (I := I) (M := M) s b).symm Φ
  have hroundtrip :
      tensor0S_curry (I := I) (M := M) s b P = Φ :=
    (tensor0S_curry (I := I) (M := M) s b).apply_symm_apply Φ
  have hev := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := P) (v0 := v) (vs := m)
  have : (show ContinuousMultilinearMap ℝ
        (fun _ : Fin s => TangentSpace I b) ℝ from
      tensor0S_curry (I := I) (M := M) s b P v) m =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from P)
        (Fin.cons v m) := hev.symm
  rw [hroundtrip] at this
  exact this.symm

omit [BoundarylessManifold I M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma LeviCivita_chartParallelExtend_eq_parallelCLM
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (v : TangentSpace I b)
    (X : Π b' : M, TangentSpace I b') :
    (LeviCivita (I := I) g).toFun
      (chartParallelExtend (I := I) α b v) b (X b) =
      chartLeviCivitaParallelCLM (I := I) g α b X v := by
  classical
  have hY_at :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b' : M => TotalSpace.mk' E
          (E := fun x : M => TangentSpace I x) b'
          (chartParallelExtend (I := I) α b v b')) b :=
    chartParallelExtend_mdifferentiableAt (I := I) α hb v
  rw [LeviCivita_chart_apply (I := I) g α hb hY_at (X b)]
  rw [chartLeviCivita_chartParallelExtend_symm (I := I) g α hb v X]
  rw [chartLeviCivitaParallelCLM_apply (I := I) g α b X v]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartTensor0SCovariantDerivative_eq_abstract_succ_aux
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ) (T : Π b' : M, Tensor0SSpace (s + 1) I b')
      (X : Π b' : M, TangentSpace I b')
      {b : M} (_hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
      (_hT_at : TensorSectionMDiffAt (I := I) (s + 1) T b)
      (_hX_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b' : M => TotalSpace.mk' E
          (E := fun x : M => TangentSpace I x) b' (X b')) b),
      chartTensor0SCovariantDerivative (I := I) (s + 1) g α T X b =
        Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
          (LeviCivita (I := I) g) T b (X b) := by
  intro s
  induction s with
  | zero =>
    intro T X b hb hT_at hX_at
    apply ContinuousMultilinearMap.ext
    intro m
    set v : TangentSpace I b := m 0 with hv_def
    have hm_decomp : m = Fin.cons v (Fin.tail m) := by
      rw [hv_def]; exact (Fin.cons_self_tail m).symm
    have htail : (Fin.tail m : Fin 0 → TangentSpace I b) =
        (fun i : Fin 0 => Fin.elim0 i) := by
      funext i; exact i.elim0
    set m₀ : Fin 0 → TangentSpace I b := fun i => Fin.elim0 i with hm0_def
    have hm_eq : m = Fin.cons v m₀ := by
      rw [hm_decomp, htail]
    rw [hm_eq]
    rw [chartTensor0SCovariantDerivative_succ_apply (I := I) 0 g α T X b
        (Fin.cons v m₀)]
    rw [tensor0SCovariantDerivative_succ_eq I M (s := 0)
        (cov := LeviCivita (I := I) g)]
    rw [tensor0SCovariantDerivative_succ_apply I M
        (s := 0)
        (cov_TM := LeviCivita (I := I) g)
        (cov_s := tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
        T b (X b)]
    rw [tensor0S_curry_symm_apply_cons (I := I) (M := M) 0
        (Φ := HomConnection.homBundleCovariantDerivativeFun I M
          (Tensor0SModel 0 ℝ E)
          (fun x : M => Tensor0SSpace 0 I x)
          (LeviCivita (I := I) g)
          (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
          (curriedSection I M T) b (X b))
        v m₀]
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
    have hYb_eq : chartParallelExtend (I := I) α b v b = v := by
      unfold chartParallelExtend
      exact trivFromE_trivToE (I := I) α hb_base v
    have hτ_at :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel 0 ℝ E))
          (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel 0 ℝ E)
            (E := fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace 0 I x)
            y (curriedSection I M T y)) b :=
      mdifferentiableAt_curriedSection_of_section (I := I) (M := M) 0 T hT_at
    have hY_at :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun y : M => TotalSpace.mk' E
            (E := fun x : M => TangentSpace I x) y
            (chartParallelExtend (I := I) α b v y)) b :=
      chartParallelExtend_mdifferentiableAt (I := I) α hb v
    have hPsi := HomConnection.homBundleCovariantDerivativeFun_apply
      (I := I) (M := M) (F := Tensor0SModel 0 ℝ E)
      (V := fun x : M => Tensor0SSpace 0 I x)
      (cov_TM := LeviCivita (I := I) g)
      (cov_V := tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
      (τ := curriedSection I M T)
      (x := b) hτ_at
      (V_field := X) (Y := chartParallelExtend (I := I) α b v)
      hX_at hY_at
    rw [hYb_eq] at hPsi
    have hPsi_explicit :
        (HomConnection.homBundleCovariantDerivativeFun I M
            (Tensor0SModel 0 ℝ E)
            (fun x : M => Tensor0SSpace 0 I x)
            (LeviCivita (I := I) g)
            (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
            (curriedSection I M T) b (X b)) v =
        ((tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
            (fun y : M => (curriedSection I M T) y
              (chartParallelExtend (I := I) α b v y)) b (X b) -
          curriedSection I M T b
            ((LeviCivita (I := I) g) (chartParallelExtend (I := I) α b v) b
              (X b)) :
          Tensor0SSpace 0 I b) := hPsi
    rw [hPsi_explicit]
    have hpair_eq :
        (fun y : M => (curriedSection I M T) y
            (chartParallelExtend (I := I) α b v y)) =
          tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v) := by
      funext y
      rfl
    rw [hpair_eq]
    rw [show ((show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b) ℝ from
          (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
            (tensor0SPartialEval I M T
              (chartParallelExtend (I := I) α b v)) b (X b) -
          curriedSection I M T b
            ((LeviCivita (I := I) g)
              (chartParallelExtend (I := I) α b v) b (X b)))) m₀ =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b) ℝ from
          (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
            (tensor0SPartialEval I M T
              (chartParallelExtend (I := I) α b v)) b (X b)) m₀ -
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b) ℝ from
          curriedSection I M T b
            ((LeviCivita (I := I) g)
              (chartParallelExtend (I := I) α b v) b (X b))) m₀ from
      ContinuousMultilinearMap.sub_apply _ _ _]
    have hslot_sum :
        (∑ k : Fin (0 + 1),
            chartTensor0SSlotCorrection (I := I) (0 + 1) g α T X b k) =
          chartTensor0SSlotCorrection (I := I) (0 + 1) g α T X b 0 := by
      simp
    rw [show ∑ k : Fin (0 + 1),
            (show ContinuousMultilinearMap ℝ
                (fun _ : Fin (0 + 1) => TangentSpace I b) ℝ from
              chartTensor0SSlotCorrection (I := I) (0 + 1) g α T X b k)
              (Fin.cons v m₀) =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (0 + 1) => TangentSpace I b) ℝ from
          chartTensor0SSlotCorrection (I := I) (0 + 1) g α T X b 0)
            (Fin.cons v m₀) from by simp]
    rw [chartTensor0SSlotCorrection_apply_localSlotCLM (I := I) (0 + 1) g α
        T X b 0 (Fin.cons v m₀)]
    have hSlot0_tuple :
        (fun i : Fin (0 + 1) =>
            localSlotCLM (I := I) (0 + 1) (0 : Fin (0 + 1))
              (chartLeviCivitaParallelCLM (I := I) g α b X) i
              ((Fin.cons v m₀ : Fin (0 + 1) → TangentSpace I b) i)) =
          (Fin.cons (chartLeviCivitaParallelCLM (I := I) g α b X v) m₀
            : Fin (0 + 1) → TangentSpace I b) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp [Fin.cons_zero, localSlotCLM]
      · intro k; exact k.elim0
    have h_cov_TM_eq : (LeviCivita (I := I) g).toFun
        (chartParallelExtend (I := I) α b v) b (X b) =
        chartLeviCivitaParallelCLM (I := I) g α b X v :=
      LeviCivita_chartParallelExtend_eq_parallelCLM (I := I) g α hb v X
    have h_curry_eval_slot0 :
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (0 + 1) => TangentSpace I b) ℝ from T b)
          (Fin.cons (chartLeviCivitaParallelCLM (I := I) g α b X v) m₀) =
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b) ℝ from
            curriedSection I M T b
              (chartLeviCivitaParallelCLM (I := I) g α b X v))
            m₀ := by
      change (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (0 + 1) => TangentSpace I b) ℝ from T b)
          (Fin.cons (chartLeviCivitaParallelCLM (I := I) g α b X v) m₀) =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b) ℝ from
          tensor0S_curry (I := I) (M := M) 0 b (T b)
            (chartLeviCivitaParallelCLM (I := I) g α b X v)) m₀
      exact (TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := T b)
        (v0 := chartLeviCivitaParallelCLM (I := I) g α b X v) (vs := m₀)).symm
    rw [hSlot0_tuple]
    rw [h_curry_eval_slot0]
    rw [show (LeviCivita (I := I) g) (chartParallelExtend (I := I) α b v) b
            (X b) = chartLeviCivitaParallelCLM (I := I) g α b X v from
      h_cov_TM_eq]
    have hRank0 :=
      chartTensor0SCovariantDerivative_eq_abstract_zero (I := I) g α
        (tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v))
        X hb
    rw [← hRank0]
    rw [chartTensor0SCovariantDerivative_zero_apply (I := I) g α
        (tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v))
        X b m₀]
    have hPartialEval_at :
        TensorSectionMDiffAt (I := I) 0
          (tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v)) b :=
      TensorSectionMDiffAt_partialEval (I := I) 0 α T hb hT_at v
    have hRank0_bridge := tensor0SIntrinsicChartCLM_zero_apply_empty_eq_mfderiv
      (I := I) α (tensor0SPartialEval I M T
        (chartParallelExtend (I := I) α b v)) hb hPartialEval_at (X b)
    rw [← hRank0_bridge]
    have hT_pull :
        DifferentiableAt ℝ
          (tensor0SChartE_section_repr (I := I) (0 + 1) α T ∘
            (extChartAt I α).symm) (extChartAt I α b) :=
      differentiableAt_tensor0SChartE_pullback_of_mdifferentiableAt
        (I := I) (0 + 1) α T hb hT_at
    have hCurryFactor :=
      tensor0SIntrinsicChartCLM_factor_via_partialEval
        (I := I) 0 α T hb v hT_pull X m₀
    have hCons_eq :
        (Fin.cons (chartParallelExtend (I := I) α b v b) m₀
          : Fin (0 + 1) → TangentSpace I b) =
          Fin.cons v m₀ := by
      rw [hYb_eq]
    rw [hCons_eq] at hCurryFactor
    rw [hCurryFactor]
  | succ s ih =>
    intro T X b hb hT_at hX_at
    apply ContinuousMultilinearMap.ext
    intro m
    set v : TangentSpace I b := m 0 with hv_def
    have hm_decomp : m = Fin.cons v (Fin.tail m) := by
      rw [hv_def]; exact (Fin.cons_self_tail m).symm
    set mt : Fin (s + 1) → TangentSpace I b := Fin.tail m with hmt_def
    have hm_eq : m = Fin.cons v mt := hm_decomp
    rw [hm_eq]
    rw [chartTensor0SCovariantDerivative_succ_apply (I := I) (s + 1) g α T X b
        (Fin.cons v mt)]
    rw [tensor0SCovariantDerivative_succ_eq I M (s := s + 1)
        (cov := LeviCivita (I := I) g)]
    rw [tensor0SCovariantDerivative_succ_apply I M
        (s := s + 1)
        (cov_TM := LeviCivita (I := I) g)
        (cov_s := tensor0SCovariantDerivative I M (s + 1)
          (LeviCivita (I := I) g))
        T b (X b)]
    rw [tensor0S_curry_symm_apply_cons (I := I) (M := M) (s + 1)
        (Φ := HomConnection.homBundleCovariantDerivativeFun I M
          (Tensor0SModel (s + 1) ℝ E)
          (fun x : M => Tensor0SSpace (s + 1) I x)
          (LeviCivita (I := I) g)
          (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
          (curriedSection I M T) b (X b))
        v mt]
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
    have hYb_eq : chartParallelExtend (I := I) α b v b = v := by
      unfold chartParallelExtend
      exact trivFromE_trivToE (I := I) α hb_base v
    have hτ_at :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel (s + 1) ℝ E))
          (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel (s + 1) ℝ E)
            (E := fun x : M =>
              TangentSpace I x →L[ℝ] Tensor0SSpace (s + 1) I x)
            y (curriedSection I M T y)) b :=
      mdifferentiableAt_curriedSection_of_section (I := I) (M := M) (s + 1)
        T hT_at
    have hY_at :
        MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun y : M => TotalSpace.mk' E
            (E := fun x : M => TangentSpace I x) y
            (chartParallelExtend (I := I) α b v y)) b :=
      chartParallelExtend_mdifferentiableAt (I := I) α hb v
    have hPsi := HomConnection.homBundleCovariantDerivativeFun_apply
      (I := I) (M := M) (F := Tensor0SModel (s + 1) ℝ E)
      (V := fun x : M => Tensor0SSpace (s + 1) I x)
      (cov_TM := LeviCivita (I := I) g)
      (cov_V := tensor0SCovariantDerivative I M (s + 1)
        (LeviCivita (I := I) g))
      (τ := curriedSection I M T)
      (x := b) hτ_at
      (V_field := X) (Y := chartParallelExtend (I := I) α b v)
      hX_at hY_at
    rw [hYb_eq] at hPsi
    have hPsi_explicit :
        (HomConnection.homBundleCovariantDerivativeFun I M
            (Tensor0SModel (s + 1) ℝ E)
            (fun x : M => Tensor0SSpace (s + 1) I x)
            (LeviCivita (I := I) g)
            (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (curriedSection I M T) b (X b)) v =
        ((tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun y : M => (curriedSection I M T) y
              (chartParallelExtend (I := I) α b v y)) b (X b) -
          curriedSection I M T b
            ((LeviCivita (I := I) g) (chartParallelExtend (I := I) α b v) b
              (X b)) :
          Tensor0SSpace (s + 1) I b) := hPsi
    rw [hPsi_explicit]
    have hpair_eq :
        (fun y : M => (curriedSection I M T) y
            (chartParallelExtend (I := I) α b v y)) =
          tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v) := by
      funext y
      rfl
    rw [hpair_eq]
    rw [show ((show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
          (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (tensor0SPartialEval I M T
              (chartParallelExtend (I := I) α b v)) b (X b) -
          curriedSection I M T b
            ((LeviCivita (I := I) g)
              (chartParallelExtend (I := I) α b v) b (X b)))) mt =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
          (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (tensor0SPartialEval I M T
              (chartParallelExtend (I := I) α b v)) b (X b)) mt -
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
          curriedSection I M T b
            ((LeviCivita (I := I) g)
              (chartParallelExtend (I := I) α b v) b (X b))) mt from
      ContinuousMultilinearMap.sub_apply _ _ _]
    rw [show ∑ k : Fin (s + 1 + 1),
            (show ContinuousMultilinearMap ℝ
                (fun _ : Fin (s + 1 + 1) => TangentSpace I b) ℝ from
              chartTensor0SSlotCorrection (I := I) (s + 1 + 1) g α T X b k)
              (Fin.cons v mt) =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1 + 1) => TangentSpace I b) ℝ from
          chartTensor0SSlotCorrection (I := I) (s + 1 + 1) g α T X b 0)
            (Fin.cons v mt) +
          ∑ k : Fin (s + 1),
            (show ContinuousMultilinearMap ℝ
                (fun _ : Fin (s + 1 + 1) => TangentSpace I b) ℝ from
              chartTensor0SSlotCorrection (I := I) (s + 1 + 1) g α T X b
                k.succ) (Fin.cons v mt) from
      Fin.sum_univ_succ _]
    rw [chartTensor0SSlotCorrection_apply_localSlotCLM (I := I) (s + 1 + 1) g α
        T X b 0 (Fin.cons v mt)]
    have hSlot0_tuple :
        (fun i : Fin (s + 1 + 1) =>
            localSlotCLM (I := I) (s + 1 + 1) (0 : Fin (s + 1 + 1))
              (chartLeviCivitaParallelCLM (I := I) g α b X) i
              ((Fin.cons v mt : Fin (s + 1 + 1) → TangentSpace I b) i)) =
          (Fin.cons (chartLeviCivitaParallelCLM (I := I) g α b X v) mt
            : Fin (s + 1 + 1) → TangentSpace I b) := by
      funext i
      refine Fin.cases ?_ ?_ i
      · simp [Fin.cons_zero, localSlotCLM]
      · intro k
        have hne : (k.succ : Fin (s + 1 + 1)) ≠ 0 := Fin.succ_ne_zero k
        simp [hne, localSlotCLM]
    rw [hSlot0_tuple]
    have hSlotSucc_sum :
        (∑ k : Fin (s + 1),
            (show ContinuousMultilinearMap ℝ
                (fun _ : Fin (s + 1 + 1) => TangentSpace I b) ℝ from
              chartTensor0SSlotCorrection (I := I) (s + 1 + 1) g α T X b
                k.succ) (Fin.cons v mt)) =
          ∑ k : Fin (s + 1),
            (show ContinuousMultilinearMap ℝ
                (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
              chartTensor0SSlotCorrection (I := I) (s + 1) g α
                (tensor0SPartialEval I M T
                  (chartParallelExtend (I := I) α b v)) X b k) mt := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact chartTensor0SSlotCorrection_succ_eq_partialEval_of_mem (I := I)
        g (s := s + 1) α T X (b := b) hb_base v k mt
    rw [hSlotSucc_sum]
    have hPartialEval_at :
        TensorSectionMDiffAt (I := I) (s + 1)
          (tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v)) b :=
      TensorSectionMDiffAt_partialEval (I := I) (s + 1) α T hb hT_at v
    have hIH := ih (tensor0SPartialEval I M T
        (chartParallelExtend (I := I) α b v))
      X hb hPartialEval_at hX_at
    rw [← hIH]
    rw [chartTensor0SCovariantDerivative_succ_apply (I := I) s g α
        (tensor0SPartialEval I M T (chartParallelExtend (I := I) α b v))
        X b mt]
    have h_cov_TM_eq :
        (LeviCivita (I := I) g) (chartParallelExtend (I := I) α b v) b (X b) =
          chartLeviCivitaParallelCLM (I := I) g α b X v :=
      LeviCivita_chartParallelExtend_eq_parallelCLM (I := I) g α hb v X
    have hT_pull :
        DifferentiableAt ℝ
          (tensor0SChartE_section_repr (I := I) (s + 1 + 1) α T ∘
            (extChartAt I α).symm) (extChartAt I α b) :=
      differentiableAt_tensor0SChartE_pullback_of_mdifferentiableAt
        (I := I) (s + 1 + 1) α T hb hT_at
    have hCurryFactor :=
      tensor0SIntrinsicChartCLM_factor_via_partialEval
        (I := I) (s + 1) α T hb v hT_pull X mt
    have hCons_eq :
        (Fin.cons (chartParallelExtend (I := I) α b v b) mt
          : Fin (s + 1 + 1) → TangentSpace I b) =
          Fin.cons v mt := by
      rw [hYb_eq]
    rw [hCons_eq] at hCurryFactor
    have h_curry_eval_slot0 :
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1 + 1) => TangentSpace I b) ℝ from T b)
          (Fin.cons (chartLeviCivitaParallelCLM (I := I) g α b X v) mt) =
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
            curriedSection I M T b
              (chartLeviCivitaParallelCLM (I := I) g α b X v))
            mt := by
      change (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1 + 1) => TangentSpace I b) ℝ from T b)
          (Fin.cons (chartLeviCivitaParallelCLM (I := I) g α b X v) mt) =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
          tensor0S_curry (I := I) (M := M) (s + 1) b (T b)
            (chartLeviCivitaParallelCLM (I := I) g α b X v)) mt
      exact (TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
        (T := T b)
        (v0 := chartLeviCivitaParallelCLM (I := I) g α b X v) (vs := mt)).symm
    rw [h_curry_eval_slot0]
    rw [h_cov_TM_eq]
    rw [hCurryFactor]
    abel

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartTensor0SCovariantDerivative_eq_abstract_succ
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M)
    (T :
      letI _h_top : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
          (fun x : M => Tensor0SSpace (s + 1) I x)) :=
        tensor0SBundle_topology (s + 1)
      letI _h_fib : FiberBundle (Tensor0SModel (s + 1) ℝ E)
          (fun x : M => Tensor0SSpace (s + 1) I x) :=
        tensor0SBundle_fiber (s + 1)
      Cₛ^∞⟮I; Tensor0SModel (s + 1) ℝ E,
        fun b => Tensor0SSpace (s + 1) I b⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartTensor0SCovariantDerivative (I := I) (s + 1) g α T.toFun X.toFun b =
      Tensor0SNabla.tensor0SCovariantDerivative I M (s + 1)
          (LeviCivita (I := I) g) T.toFun b (X.toFun b) := by
  classical
  letI _h_top : TopologicalSpace (TotalSpace (Tensor0SModel (s + 1) ℝ E)
      (fun x : M => Tensor0SSpace (s + 1) I x)) :=
    tensor0SBundle_topology (s + 1)
  letI _h_fib : FiberBundle (Tensor0SModel (s + 1) ℝ E)
      (fun x : M => Tensor0SSpace (s + 1) I x) :=
    tensor0SBundle_fiber (s + 1)
  have hT_at : TensorSectionMDiffAt (I := I) (s + 1) T.toFun b := by
    unfold TensorSectionMDiffAt
    exact T.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hX_at :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun b' : M => TotalSpace.mk' E
          (E := fun x : M => TangentSpace I x) b' (X.toFun b')) b :=
    X.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  exact chartTensor0SCovariantDerivative_eq_abstract_succ_aux
    (I := I) (M := M) g α s T.toFun X.toFun hb hT_at hX_at

end Connection
end Integral
end DifferentialGeometry

end
