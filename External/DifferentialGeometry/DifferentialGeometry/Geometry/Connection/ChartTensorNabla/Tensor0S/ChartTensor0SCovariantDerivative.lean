import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SChartChristoffel
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannian


noncomputable section

open Bundle Manifold Set
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

def chartParallelExtend (α b : M) (v : TangentSpace I b) (b' : M) :
    TangentSpace I b' :=
  trivFromE (I := I) α b' (trivToE (I := I) α b v)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartParallelExtend_def (α b : M) (v : TangentSpace I b) (b' : M) :
    chartParallelExtend (I := I) α b v b' =
      trivFromE (I := I) α b' (trivToE (I := I) α b v) := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartE_section_repr_chartParallelExtend
    (α b : M) (v : TangentSpace I b) {b' : M}
    (hb' : b' ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartE_section_repr (I := I) α
        (chartParallelExtend (I := I) α b v) b' =
      trivToE (I := I) α b v := by
  classical
  unfold chartParallelExtend
  change trivToE (I := I) α b' (trivFromE (I := I) α b' (trivToE (I := I) α b v))
      = trivToE (I := I) α b v
  exact trivToE_trivFromE (I := I) α hb' _

def chartLeviCivitaParallelCLM
    (g : SmoothRiemannianMetric I M) (α b : M)
    (X : Π b' : M, TangentSpace I b') :
    TangentSpace I b →L[ℝ] TangentSpace I b :=
  (trivFromE (I := I) α b).comp
    (christoffelCorrection (I := I) g α b
      (trivToE (I := I) α b (X b)))

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartLeviCivitaParallelCLM_apply
    (g : SmoothRiemannianMetric I M) (α b : M)
    (X : Π b' : M, TangentSpace I b') (v : TangentSpace I b) :
    chartLeviCivitaParallelCLM (I := I) g α b X v =
      trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b (X b)) v) := by
  classical
  unfold chartLeviCivitaParallelCLM
  rfl

private def slotCLM (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (i : Fin s) : TangentSpace I b →L[ℝ] TangentSpace I b :=
  if i = k then Φ else ContinuousLinearMap.id ℝ (TangentSpace I b)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private lemma slotCLM_self (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) :
    slotCLM (I := I) s k Φ k = Φ := by
  unfold slotCLM
  simp

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
private lemma slotCLM_other (s : ℕ) {b : M}
    (k : Fin s) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    {i : Fin s} (h : i ≠ k) :
    slotCLM (I := I) s k Φ i = ContinuousLinearMap.id ℝ (TangentSpace I b) := by
  unfold slotCLM
  simp [h]

def chartTensor0SSlotCorrection (s : ℕ) (g : SmoothRiemannianMetric I M)
    (α : M) (T : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s) :
    Tensor0SSpace s I b :=
  ContinuousMultilinearMap.compContinuousLinearMap
    (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I b) ℝ from T b)
    (slotCLM (I := I) s k (chartLeviCivitaParallelCLM (I := I) g α b X))

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SSlotCorrection_apply (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s)
    (m : Fin s → TangentSpace I b) :
    chartTensor0SSlotCorrection (I := I) s g α T X b k m =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin s => TangentSpace I b) ℝ from T b)
        (fun i =>
          slotCLM (I := I) s k
              (chartLeviCivitaParallelCLM (I := I) g α b X) i (m i)) := by
  classical
  unfold chartTensor0SSlotCorrection
  rfl

def chartTensor0SCovariantDerivative :
    (s : ℕ) → SmoothRiemannianMetric I M → (α : M) →
      (T : Π b : M, Tensor0SSpace s I b) →
      (X : Π b : M, TangentSpace I b) →
      (b : M) → Tensor0SSpace s I b
  | 0, _g, _α, T, X, b =>
      (show ContinuousMultilinearMap ℝ (fun _ : Fin 0 => TangentSpace I b) ℝ from
        ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I b)
          (mfderiv I 𝓘(ℝ) (fun b' : M =>
              (show ContinuousMultilinearMap ℝ
                  (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
              (fun i => Fin.elim0 i)) b (X b)))
  | s + 1, g, α, T, X, b =>
      tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b)
        - ∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_zero
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace 0 I b)
    (X : Π b : M, TangentSpace I b) (b : M) :
    chartTensor0SCovariantDerivative (I := I) 0 g α T X b =
      (show ContinuousMultilinearMap ℝ (fun _ : Fin 0 => TangentSpace I b) ℝ from
        ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I b)
          (mfderiv I 𝓘(ℝ) (fun b' : M =>
              (show ContinuousMultilinearMap ℝ
                  (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
              (fun i => Fin.elim0 i)) b (X b))) := rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_succ (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (X : Π b : M, TangentSpace I b) (b : M) :
    chartTensor0SCovariantDerivative (I := I) (s + 1) g α T X b =
      tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b)
        - ∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k := rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_zero_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace 0 I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (m : Fin 0 → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ (fun _ : Fin 0 => TangentSpace I b) ℝ from
      chartTensor0SCovariantDerivative (I := I) 0 g α T X b) m =
      mfderiv I 𝓘(ℝ) (fun b' : M =>
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
        (fun i => Fin.elim0 i)) b (X b) := by
  classical
  rw [chartTensor0SCovariantDerivative_zero]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_succ_apply (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (m : Fin (s + 1) → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
      chartTensor0SCovariantDerivative (I := I) (s + 1) g α T X b) m =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
        tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b)) m
      - ∑ k : Fin (s + 1),
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) m := by
  classical
  rw [chartTensor0SCovariantDerivative_succ]
  rw [show (show ContinuousMultilinearMap ℝ
        (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
        tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b)
          - ∑ k : Fin (s + 1),
              chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) m =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
        tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b)) m
      - (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
        ∑ k : Fin (s + 1),
          chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) m by
    rfl]
  congr 1
  set Y : Fin (s + 1) → Tensor0SSpace (s + 1) I b :=
    fun k => chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k
  have hY : (∑ k : Fin (s + 1), Y k) = ∑ k : Fin (s + 1), Y k := rfl
  change (show ContinuousMultilinearMap ℝ
          (fun _ : Fin (s + 1) => TangentSpace I b) ℝ from
        ∑ k : Fin (s + 1), Y k) m = _
  rw [ContinuousMultilinearMap.sum_apply]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_zero_add
    (g : SmoothRiemannianMetric I M) (α : M)
    (T₁ T₂ : Π b : M, Tensor0SSpace 0 I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (h₁ : MDiffAt
        (fun b' : M =>
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b') ℝ from T₁ b')
          (fun i => Fin.elim0 i)) b)
    (h₂ : MDiffAt
        (fun b' : M =>
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b') ℝ from T₂ b')
          (fun i => Fin.elim0 i)) b) :
    chartTensor0SCovariantDerivative (I := I) 0 g α (T₁ + T₂) X b =
      chartTensor0SCovariantDerivative (I := I) 0 g α T₁ X b
        + chartTensor0SCovariantDerivative (I := I) 0 g α T₂ X b := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  have hRHS :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin 0 => TangentSpace I b) ℝ from
        chartTensor0SCovariantDerivative (I := I) 0 g α T₁ X b
          + chartTensor0SCovariantDerivative (I := I) 0 g α T₂ X b) m =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b) ℝ from
          chartTensor0SCovariantDerivative (I := I) 0 g α T₁ X b) m
          + (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b) ℝ from
            chartTensor0SCovariantDerivative (I := I) 0 g α T₂ X b) m := by
    rfl
  rw [hRHS]
  rw [chartTensor0SCovariantDerivative_zero_apply,
      chartTensor0SCovariantDerivative_zero_apply,
      chartTensor0SCovariantDerivative_zero_apply]
  have hpw :
      (fun b' : M =>
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b') ℝ from (T₁ + T₂) b')
          (fun i => Fin.elim0 i)) =
        (fun b' : M =>
            (show ContinuousMultilinearMap ℝ
                (fun _ : Fin 0 => TangentSpace I b') ℝ from T₁ b')
            (fun i => Fin.elim0 i)) +
          (fun b' : M =>
              (show ContinuousMultilinearMap ℝ
                  (fun _ : Fin 0 => TangentSpace I b') ℝ from T₂ b')
              (fun i => Fin.elim0 i)) := by
    funext b'
    exact ContinuousMultilinearMap.add_apply
      (f := (T₁ b' : ContinuousMultilinearMap ℝ
        (fun _ : Fin 0 => TangentSpace I b') ℝ))
      (f' := (T₂ b' : ContinuousMultilinearMap ℝ
        (fun _ : Fin 0 => TangentSpace I b') ℝ))
      (fun i : Fin 0 => Fin.elim0 i)
  rw [hpw]
  rw [mfderiv_add h₁ h₂]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_zero_smul
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (T : Π b : M, Tensor0SSpace 0 I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (hT : MDiffAt
        (fun b' : M =>
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
          (fun i => Fin.elim0 i)) b) :
    chartTensor0SCovariantDerivative (I := I) 0 g α (c • T) X b =
      c • chartTensor0SCovariantDerivative (I := I) 0 g α T X b := by
  classical
  apply ContinuousMultilinearMap.ext
  intro m
  have hRHS :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin 0 => TangentSpace I b) ℝ from
        c • chartTensor0SCovariantDerivative (I := I) 0 g α T X b) m =
        c • (show ContinuousMultilinearMap ℝ
            (fun _ : Fin 0 => TangentSpace I b) ℝ from
          chartTensor0SCovariantDerivative (I := I) 0 g α T X b) m := by
    rfl
  rw [hRHS]
  rw [chartTensor0SCovariantDerivative_zero_apply,
      chartTensor0SCovariantDerivative_zero_apply]
  have hpw :
      (fun b' : M =>
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin 0 => TangentSpace I b') ℝ from (c • T) b')
          (fun i => Fin.elim0 i)) =
        c • (fun b' : M =>
            (show ContinuousMultilinearMap ℝ
                (fun _ : Fin 0 => TangentSpace I b') ℝ from T b')
            (fun i => Fin.elim0 i)) := by
    funext b'
    exact ContinuousMultilinearMap.smul_apply
      (f := (T b' : ContinuousMultilinearMap ℝ
        (fun _ : Fin 0 => TangentSpace I b') ℝ)) c
      (fun i : Fin 0 => Fin.elim0 i)
  rw [hpw]
  rw [const_smul_mfderiv hT c]
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SSlotCorrection_add (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T₁ T₂ : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s) :
    chartTensor0SSlotCorrection (I := I) s g α (T₁ + T₂) X b k =
      chartTensor0SSlotCorrection (I := I) s g α T₁ X b k
        + chartTensor0SSlotCorrection (I := I) s g α T₂ X b k := by
  classical
  unfold chartTensor0SSlotCorrection
  have hT_add : ((T₁ + T₂) b
        : ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ) =
      (T₁ b : ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ)
        + (T₂ b : ContinuousMultilinearMap ℝ
            (fun _ : Fin s => TangentSpace I b) ℝ) := by
    rfl
  rw [hT_add]
  apply ContinuousMultilinearMap.ext
  intro m
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SSlotCorrection_smul (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (T : Π b' : M, Tensor0SSpace s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin s) :
    chartTensor0SSlotCorrection (I := I) s g α (c • T) X b k =
      c • chartTensor0SSlotCorrection (I := I) s g α T X b k := by
  classical
  unfold chartTensor0SSlotCorrection
  have hT_smul : ((c • T) b
        : ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ) =
      c • (T b : ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ) := by
    rfl
  rw [hT_smul]
  apply ContinuousMultilinearMap.ext
  intro m
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_succ_add (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T₁ T₂ : Π b : M, Tensor0SSpace (s + 1) I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (h₁ : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) (s + 1) α T₁ ∘ (extChartAt I α).symm)
      (extChartAt I α b))
    (h₂ : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) (s + 1) α T₂ ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    chartTensor0SCovariantDerivative (I := I) (s + 1) g α (T₁ + T₂) X b =
      chartTensor0SCovariantDerivative (I := I) (s + 1) g α T₁ X b
        + chartTensor0SCovariantDerivative (I := I) (s + 1) g α T₂ X b := by
  classical
  rw [chartTensor0SCovariantDerivative_succ,
      chartTensor0SCovariantDerivative_succ,
      chartTensor0SCovariantDerivative_succ]
  have hsplit_intrinsic :
      tensor0SIntrinsicChartCLM (I := I) (s + 1) α (T₁ + T₂) b (X b) =
        tensor0SIntrinsicChartCLM (I := I) (s + 1) α T₁ b (X b) +
          tensor0SIntrinsicChartCLM (I := I) (s + 1) α T₂ b (X b) := by
    have hCLM := tensor0SIntrinsicChartCLM_add_section
      (I := I) (s + 1) α T₁ T₂ b h₁ h₂
    have := congrArg (fun L : TangentSpace I b →L[ℝ] Tensor0SSpace (s + 1) I b
                        => L (X b)) hCLM
    simpa using this
  rw [hsplit_intrinsic]
  have hsplit_slot :
      (∑ k : Fin (s + 1),
          chartTensor0SSlotCorrection (I := I) (s + 1) g α (T₁ + T₂) X b k) =
        (∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T₁ X b k) +
          (∑ k : Fin (s + 1),
              chartTensor0SSlotCorrection (I := I) (s + 1) g α T₂ X b k) := by
    rw [show (∑ k : Fin (s + 1),
          chartTensor0SSlotCorrection (I := I) (s + 1) g α (T₁ + T₂) X b k) =
        ∑ k : Fin (s + 1),
          (chartTensor0SSlotCorrection (I := I) (s + 1) g α T₁ X b k
            + chartTensor0SSlotCorrection (I := I) (s + 1) g α T₂ X b k) from
      Finset.sum_congr rfl (fun k _ =>
        chartTensor0SSlotCorrection_add (I := I) (s + 1) g α T₁ T₂ X b k)]
    exact Finset.sum_add_distrib
      (f := fun k : Fin (s + 1) =>
        chartTensor0SSlotCorrection (I := I) (s + 1) g α T₁ X b k)
      (g := fun k : Fin (s + 1) =>
        chartTensor0SSlotCorrection (I := I) (s + 1) g α T₂ X b k)
  rw [hsplit_slot]
  abel

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensor0SCovariantDerivative_succ_smul (s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (T : Π b : M, Tensor0SSpace (s + 1) I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (hT : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) (s + 1) α T ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    chartTensor0SCovariantDerivative (I := I) (s + 1) g α (c • T) X b =
      c • chartTensor0SCovariantDerivative (I := I) (s + 1) g α T X b := by
  classical
  rw [chartTensor0SCovariantDerivative_succ,
      chartTensor0SCovariantDerivative_succ]
  have hsplit_intrinsic :
      tensor0SIntrinsicChartCLM (I := I) (s + 1) α (c • T) b (X b) =
        c • tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b) := by
    have hCLM := tensor0SIntrinsicChartCLM_smul_section
      (I := I) (s + 1) α c T b hT
    have := congrArg (fun L : TangentSpace I b →L[ℝ] Tensor0SSpace (s + 1) I b
                        => L (X b)) hCLM
    simpa using this
  rw [hsplit_intrinsic]
  have hsplit_slot :
      (∑ k : Fin (s + 1),
          chartTensor0SSlotCorrection (I := I) (s + 1) g α (c • T) X b k) =
        c • (∑ k : Fin (s + 1),
              chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) := by
    have hterm :
        (∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α (c • T) X b k) =
          ∑ k : Fin (s + 1),
            c • chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact chartTensor0SSlotCorrection_smul (I := I) (s + 1) g α c T X b k
    rw [hterm]
    classical
    have hmap :
        c • (∑ k : Fin (s + 1),
              chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) =
          ∑ k : Fin (s + 1),
            c • chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k := by
      have hLM := map_sum (LinearMap.lsmul ℝ (Tensor0SSpace (s + 1) I b) c)
          (fun k => chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k)
          Finset.univ
      exact hLM
    rw [hmap]
  rw [hsplit_slot]
  have hsub :
      c • (tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b) (X b)
        - c • (∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) =
      c • ((tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b) (X b)
        - ∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k) :=
    ((LinearMap.lsmul ℝ (Tensor0SSpace (s + 1) I b) c).map_sub
        (tensor0SIntrinsicChartCLM (I := I) (s + 1) α T b (X b))
        (∑ k : Fin (s + 1),
            chartTensor0SSlotCorrection (I := I) (s + 1) g α T X b k)).symm
  exact hsub

end Connection
end Integral
end DifferentialGeometry
