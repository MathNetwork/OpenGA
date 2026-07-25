import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.ChartTensor0SCovariantDerivative
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Tensor0S.Tensor0SChartChristoffel
import DifferentialGeometry.Tensor.RSTensor.Defs


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators
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

noncomputable def tensorRSChartE_section_repr (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b) (b : M) : TensorRSModel r s ℝ E :=
  (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma tensorRSChartE_section_repr_apply (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b) (b : M) :
    tensorRSChartE_section_repr (I := I) r s α T b =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b) :=
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensorRSChartE_section_repr_add (r s : ℕ) (α : M)
    (T₁ T₂ : Π b : M, TensorRSSpace r s I b) :
    tensorRSChartE_section_repr (I := I) r s α (T₁ + T₂) =
      tensorRSChartE_section_repr (I := I) r s α T₁ +
        tensorRSChartE_section_repr (I := I) r s α T₂ := by
  funext b
  unfold tensorRSChartE_section_repr
  change (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ((T₁ + T₂) b) = _
  change (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (T₁ b + T₂ b) = _
  exact map_add _ (T₁ b) (T₂ b)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensorRSChartE_section_repr_smul (r s : ℕ) (α : M) (c : ℝ)
    (T : Π b : M, TensorRSSpace r s I b) :
    tensorRSChartE_section_repr (I := I) r s α (c • T) =
      c • tensorRSChartE_section_repr (I := I) r s α T := by
  funext b
  unfold tensorRSChartE_section_repr
  change (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        ((c • T) b) = _
  change (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
        (c • T b) = _
  exact map_smul _ c (T b)

noncomputable def tensorRSChartFiberFromModel (r s : ℕ) (α : M) (b : M) :
    TensorRSModel r s ℝ E →L[ℝ] TensorRSSpace r s I b :=
  (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b

noncomputable def tensorRSIntrinsicChartCLM (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b) (b : M) :
    TangentSpace I b →L[ℝ] TensorRSSpace r s I b :=
  (tensorRSChartFiberFromModel (I := I) r s α b).comp
    ((fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α T ∘ (extChartAt I α).symm)
        (extChartAt I α b)).comp
      (trivToE (I := I) α b))

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensorRSIntrinsicChartCLM_apply (r s : ℕ) (α : M)
    (T : Π b : M, TensorRSSpace r s I b) (b : M) (v : TangentSpace I b) :
    tensorRSIntrinsicChartCLM (I := I) r s α T b v =
      tensorRSChartFiberFromModel (I := I) r s α b
        (fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α T ∘ (extChartAt I α).symm)
          (extChartAt I α b) (trivToE (I := I) α b v)) := by
  classical
  unfold tensorRSIntrinsicChartCLM
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensorRSIntrinsicChartCLM_add_section (r s : ℕ) (α : M)
    (T₁ T₂ : Π b : M, TensorRSSpace r s I b) (b : M)
    (h₁ : DifferentiableAt ℝ
      (tensorRSChartE_section_repr (I := I) r s α T₁ ∘ (extChartAt I α).symm)
      (extChartAt I α b))
    (h₂ : DifferentiableAt ℝ
      (tensorRSChartE_section_repr (I := I) r s α T₂ ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    tensorRSIntrinsicChartCLM (I := I) r s α (T₁ + T₂) b =
      tensorRSIntrinsicChartCLM (I := I) r s α T₁ b +
        tensorRSIntrinsicChartCLM (I := I) r s α T₂ b := by
  classical
  have hsum_pull :
      (tensorRSChartE_section_repr (I := I) r s α (T₁ + T₂) ∘
          (extChartAt I α).symm) =
        (tensorRSChartE_section_repr (I := I) r s α T₁ ∘
            (extChartAt I α).symm) +
          (tensorRSChartE_section_repr (I := I) r s α T₂ ∘
            (extChartAt I α).symm) := by
    funext y
    exact congrFun (tensorRSChartE_section_repr_add (I := I) r s α T₁ T₂)
      ((extChartAt I α).symm y)
  have hfd : fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α (T₁ + T₂) ∘
          (extChartAt I α).symm) (extChartAt I α b) =
      fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α T₁ ∘
            (extChartAt I α).symm) (extChartAt I α b) +
        fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α T₂ ∘
            (extChartAt I α).symm) (extChartAt I α b) := by
    rw [hsum_pull]
    exact fderiv_add h₁ h₂
  unfold tensorRSIntrinsicChartCLM
  rw [hfd]
  ext v
  rw [ContinuousLinearMap.add_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.add_apply, map_add]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensorRSIntrinsicChartCLM_smul_section (r s : ℕ) (α : M)
    (c : ℝ) (T : Π b : M, TensorRSSpace r s I b) (b : M)
    (hT : DifferentiableAt ℝ
      (tensorRSChartE_section_repr (I := I) r s α T ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    tensorRSIntrinsicChartCLM (I := I) r s α (c • T) b =
      c • tensorRSIntrinsicChartCLM (I := I) r s α T b := by
  classical
  have hsmul_pull :
      (tensorRSChartE_section_repr (I := I) r s α (c • T) ∘
          (extChartAt I α).symm) =
        c • (tensorRSChartE_section_repr (I := I) r s α T ∘
          (extChartAt I α).symm) := by
    funext y
    exact congrFun (tensorRSChartE_section_repr_smul (I := I) r s α c T)
      ((extChartAt I α).symm y)
  have hfd : fderiv ℝ
        (tensorRSChartE_section_repr (I := I) r s α (c • T) ∘
          (extChartAt I α).symm) (extChartAt I α b) =
      c • fderiv ℝ
          (tensorRSChartE_section_repr (I := I) r s α T ∘
            (extChartAt I α).symm) (extChartAt I α b) := by
    rw [hsmul_pull]
    exact fderiv_const_smul hT c
  unfold tensorRSIntrinsicChartCLM
  rw [hfd]
  ext v
  rw [ContinuousLinearMap.smul_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.smul_apply, map_smul]

def tangentSlotCLM (n : ℕ) {b : M}
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (i : Fin n) : TangentSpace I b →L[ℝ] TangentSpace I b :=
  if i = k then Φ else ContinuousLinearMap.id ℝ (TangentSpace I b)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
lemma tangentSlotCLM_self (n : ℕ) {b : M}
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) :
    tangentSlotCLM (I := I) n k Φ k = Φ := by
  unfold tangentSlotCLM
  simp

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
lemma tangentSlotCLM_other (n : ℕ) {b : M}
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    {i : Fin n} (h : i ≠ k) :
    tangentSlotCLM (I := I) n k Φ i = ContinuousLinearMap.id ℝ (TangentSpace I b) := by
  unfold tangentSlotCLM
  simp [h]

noncomputable def tangentCompCLML_E (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ :=
  ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ)
    (show Fin n → (E →L[ℝ] E) from Φ)

noncomputable def tensorSlotSubstCLM (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b)) :
    Tensor0SSpace n I b →L[ℝ] Tensor0SSpace n I b :=
  ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b).symm
      : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ →L[ℝ]
          Tensor0SSpace n I b).comp
    ((tangentCompCLML_E (I := I) (M := M) n b Φ).comp
      ((tensor0SSpace_continuousLinearEquiv (I := I) (M := M) n b)
          : Tensor0SSpace n I b →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensorSlotSubstCLM_apply (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b))
    (τ : Tensor0SSpace n I b) (m : Fin n → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin n => TangentSpace I b) ℝ from
      tensorSlotSubstCLM (I := I) n b Φ τ) m =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin n => TangentSpace I b) ℝ from τ)
        (fun i => Φ i (m i)) := by
  classical
  unfold tensorSlotSubstCLM tangentCompCLML_E
  rfl

noncomputable def chartTensorRSInputSlotCorrection (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin r) :
    TensorRSSpace r s I b :=
  (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b).comp
    (tensorSlotSubstCLM (I := I) r b
      (tangentSlotCLM (I := I) r k
        (chartLeviCivitaParallelCLM (I := I) g α b X)))

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSInputSlotCorrection_apply (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin r)
    (α_input : Tensor0SSpace r I b) (m : Fin s → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin s => TangentSpace I b) ℝ from
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
        chartTensorRSInputSlotCorrection (I := I) r s g α T X b k)
        α_input) m =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)
          (tensorSlotSubstCLM (I := I) r b
            (tangentSlotCLM (I := I) r k
              (chartLeviCivitaParallelCLM (I := I) g α b X)) α_input)) m := by
  classical
  unfold chartTensorRSInputSlotCorrection
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSInputSlotCorrection_add (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T₁ T₂ : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin r) :
    chartTensorRSInputSlotCorrection (I := I) r s g α (T₁ + T₂) X b k =
      chartTensorRSInputSlotCorrection (I := I) r s g α T₁ X b k
        + chartTensorRSInputSlotCorrection (I := I) r s g α T₂ X b k := by
  classical
  unfold chartTensorRSInputSlotCorrection
  have hT_add : ((T₁ + T₂) b
      : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
      (T₁ b : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        + (T₂ b : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) := rfl
  rw [hT_add]
  exact ContinuousLinearMap.add_comp _ _ _

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSInputSlotCorrection_smul (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (k : Fin r) :
    chartTensorRSInputSlotCorrection (I := I) r s g α (c • T) X b k =
      c • chartTensorRSInputSlotCorrection (I := I) r s g α T X b k := by
  classical
  unfold chartTensorRSInputSlotCorrection
  have hT_smul : ((c • T) b
      : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
      c • (T b : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) := rfl
  rw [hT_smul]
  exact ContinuousLinearMap.smul_comp _ _ _

noncomputable def chartTensorRSOutputSlotCorrection (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (l : Fin s) :
    TensorRSSpace r s I b :=
  (tensorSlotSubstCLM (I := I) s b
      (tangentSlotCLM (I := I) s l
        (chartLeviCivitaParallelCLM (I := I) g α b X))).comp
    (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSOutputSlotCorrection_apply (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (l : Fin s)
    (α_input : Tensor0SSpace r I b) (m : Fin s → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin s => TangentSpace I b) ℝ from
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
        chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l)
        α_input) m =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) α_input)
        (fun i =>
          tangentSlotCLM (I := I) s l
            (chartLeviCivitaParallelCLM (I := I) g α b X) i (m i)) := by
  classical
  unfold chartTensorRSOutputSlotCorrection
  rw [ContinuousLinearMap.comp_apply]
  exact tensorSlotSubstCLM_apply (I := I) s b
    (tangentSlotCLM (I := I) s l
      (chartLeviCivitaParallelCLM (I := I) g α b X))
    ((show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from T b) α_input) m

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSOutputSlotCorrection_add (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T₁ T₂ : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (l : Fin s) :
    chartTensorRSOutputSlotCorrection (I := I) r s g α (T₁ + T₂) X b l =
      chartTensorRSOutputSlotCorrection (I := I) r s g α T₁ X b l
        + chartTensorRSOutputSlotCorrection (I := I) r s g α T₂ X b l := by
  classical
  unfold chartTensorRSOutputSlotCorrection
  have hT_add : ((T₁ + T₂) b
      : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
      (T₁ b : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b)
        + (T₂ b : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) := rfl
  rw [hT_add]
  exact ContinuousLinearMap.comp_add _ _ _

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSOutputSlotCorrection_smul (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X : Π b' : M, TangentSpace I b') (b : M) (l : Fin s) :
    chartTensorRSOutputSlotCorrection (I := I) r s g α (c • T) X b l =
      c • chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l := by
  classical
  unfold chartTensorRSOutputSlotCorrection
  have hT_smul : ((c • T) b
      : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) =
      c • (T b : Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b) := rfl
  rw [hT_smul]
  exact ContinuousLinearMap.comp_smul _ _ _

noncomputable def chartTensorRSCovariantDerivative (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, TensorRSSpace r s I b)
    (X : Π b : M, TangentSpace I b) (b : M) : TensorRSSpace r s I b :=
  tensorRSIntrinsicChartCLM (I := I) r s α T b (X b)
    + (∑ k : Fin r,
        chartTensorRSInputSlotCorrection (I := I) r s g α T X b k)
    - (∑ l : Fin s,
        chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSCovariantDerivative_def (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, TensorRSSpace r s I b)
    (X : Π b : M, TangentSpace I b) (b : M) :
    chartTensorRSCovariantDerivative (I := I) r s g α T X b =
      tensorRSIntrinsicChartCLM (I := I) r s α T b (X b)
        + (∑ k : Fin r,
            chartTensorRSInputSlotCorrection (I := I) r s g α T X b k)
        - (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l) := rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSCovariantDerivative_apply (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, TensorRSSpace r s I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (α_input : Tensor0SSpace r I b) (m : Fin s → TangentSpace I b) :
    (show ContinuousMultilinearMap ℝ
        (fun _ : Fin s => TangentSpace I b) ℝ from
      (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
        chartTensorRSCovariantDerivative (I := I) r s g α T X b)
        α_input) m =
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          tensorRSIntrinsicChartCLM (I := I) r s α T b (X b))
          α_input) m
      + ∑ k : Fin r,
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I b) ℝ from
            (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              chartTensorRSInputSlotCorrection (I := I) r s g α T X b k)
              α_input) m
      - ∑ l : Fin s,
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I b) ℝ from
            (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l)
              α_input) m := by
  classical
  rw [chartTensorRSCovariantDerivative_def]
  set Bsum : TensorRSSpace r s I b :=
      ∑ k : Fin r,
        chartTensorRSInputSlotCorrection (I := I) r s g α T X b k with hBdef
  set Csum : TensorRSSpace r s I b :=
      ∑ l : Fin s,
        chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l with hCdef
  have hstep1 :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
          tensorRSIntrinsicChartCLM (I := I) r s α T b (X b) + Bsum - Csum)
          α_input) m =
        (show ContinuousMultilinearMap ℝ
            (fun _ : Fin s => TangentSpace I b) ℝ from
          (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
            tensorRSIntrinsicChartCLM (I := I) r s α T b (X b))
            α_input) m
        + (show ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I b) ℝ from
            (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Bsum) α_input) m
        - (show ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I b) ℝ from
            (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Csum) α_input) m :=
    rfl
  rw [hstep1]
  have hBeval :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Bsum) α_input) m =
      ∑ k : Fin r,
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I b) ℝ from
            (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              chartTensorRSInputSlotCorrection (I := I) r s g α T X b k)
              α_input) m := by
    rw [hBdef]
    rw [ContinuousLinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]
  have hCeval :
      (show ContinuousMultilinearMap ℝ
          (fun _ : Fin s => TangentSpace I b) ℝ from
        (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from Csum) α_input) m =
      ∑ l : Fin s,
          (show ContinuousMultilinearMap ℝ
              (fun _ : Fin s => TangentSpace I b) ℝ from
            (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from
              chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l)
              α_input) m := by
    rw [hCdef]
    rw [ContinuousLinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]
  rw [hBeval, hCeval]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSCovariantDerivative_add (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M)
    (T₁ T₂ : Π b : M, TensorRSSpace r s I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (h₁ : DifferentiableAt ℝ
      (tensorRSChartE_section_repr (I := I) r s α T₁ ∘ (extChartAt I α).symm)
      (extChartAt I α b))
    (h₂ : DifferentiableAt ℝ
      (tensorRSChartE_section_repr (I := I) r s α T₂ ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    chartTensorRSCovariantDerivative (I := I) r s g α (T₁ + T₂) X b =
      chartTensorRSCovariantDerivative (I := I) r s g α T₁ X b
        + chartTensorRSCovariantDerivative (I := I) r s g α T₂ X b := by
  classical
  rw [chartTensorRSCovariantDerivative_def,
      chartTensorRSCovariantDerivative_def,
      chartTensorRSCovariantDerivative_def]
  have hsplit_intrinsic :
      tensorRSIntrinsicChartCLM (I := I) r s α (T₁ + T₂) b (X b) =
        tensorRSIntrinsicChartCLM (I := I) r s α T₁ b (X b)
          + tensorRSIntrinsicChartCLM (I := I) r s α T₂ b (X b) := by
    have hCLM := tensorRSIntrinsicChartCLM_add_section
      (I := I) r s α T₁ T₂ b h₁ h₂
    have := congrArg (fun L : TangentSpace I b →L[ℝ] TensorRSSpace r s I b
                        => L (X b)) hCLM
    simpa using this
  rw [hsplit_intrinsic]
  have hsplit_input :
      (∑ k : Fin r,
          chartTensorRSInputSlotCorrection (I := I) r s g α (T₁ + T₂) X b k) =
        (∑ k : Fin r,
            chartTensorRSInputSlotCorrection (I := I) r s g α T₁ X b k) +
          (∑ k : Fin r,
              chartTensorRSInputSlotCorrection (I := I) r s g α T₂ X b k) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact chartTensorRSInputSlotCorrection_add (I := I) r s g α T₁ T₂ X b k
  rw [hsplit_input]
  have hsplit_output :
      (∑ l : Fin s,
          chartTensorRSOutputSlotCorrection (I := I) r s g α (T₁ + T₂) X b l) =
        (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α T₁ X b l) +
          (∑ l : Fin s,
              chartTensorRSOutputSlotCorrection (I := I) r s g α T₂ X b l) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    exact chartTensorRSOutputSlotCorrection_add (I := I) r s g α T₁ T₂ X b l
  rw [hsplit_output]
  abel

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma chartTensorRSCovariantDerivative_smul (r s : ℕ)
    (g : SmoothRiemannianMetric I M) (α : M) (c : ℝ)
    (T : Π b : M, TensorRSSpace r s I b)
    (X : Π b : M, TangentSpace I b) (b : M)
    (hT : DifferentiableAt ℝ
      (tensorRSChartE_section_repr (I := I) r s α T ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    chartTensorRSCovariantDerivative (I := I) r s g α (c • T) X b =
      c • chartTensorRSCovariantDerivative (I := I) r s g α T X b := by
  classical
  rw [chartTensorRSCovariantDerivative_def,
      chartTensorRSCovariantDerivative_def]
  have hsplit_intrinsic :
      tensorRSIntrinsicChartCLM (I := I) r s α (c • T) b (X b) =
        c • tensorRSIntrinsicChartCLM (I := I) r s α T b (X b) := by
    have hCLM := tensorRSIntrinsicChartCLM_smul_section
      (I := I) r s α c T b hT
    have := congrArg (fun L : TangentSpace I b →L[ℝ] TensorRSSpace r s I b
                        => L (X b)) hCLM
    simpa using this
  rw [hsplit_intrinsic]
  have hsplit_input :
      (∑ k : Fin r,
          chartTensorRSInputSlotCorrection (I := I) r s g α (c • T) X b k) =
        c • (∑ k : Fin r,
              chartTensorRSInputSlotCorrection (I := I) r s g α T X b k) := by
    have hterm :
        (∑ k : Fin r,
            chartTensorRSInputSlotCorrection (I := I) r s g α (c • T) X b k) =
          ∑ k : Fin r,
            c • chartTensorRSInputSlotCorrection (I := I) r s g α T X b k := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      exact chartTensorRSInputSlotCorrection_smul (I := I) r s g α c T X b k
    rw [hterm]
    classical
    have hmap :=
      map_sum (LinearMap.lsmul ℝ (TensorRSSpace r s I b) c)
        (fun k => chartTensorRSInputSlotCorrection (I := I) r s g α T X b k)
        Finset.univ
    exact hmap.symm
  rw [hsplit_input]
  have hsplit_output :
      (∑ l : Fin s,
          chartTensorRSOutputSlotCorrection (I := I) r s g α (c • T) X b l) =
        c • (∑ l : Fin s,
              chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l) := by
    have hterm :
        (∑ l : Fin s,
            chartTensorRSOutputSlotCorrection (I := I) r s g α (c • T) X b l) =
          ∑ l : Fin s,
            c • chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      exact chartTensorRSOutputSlotCorrection_smul (I := I) r s g α c T X b l
    rw [hterm]
    classical
    have hmap :=
      map_sum (LinearMap.lsmul ℝ (TensorRSSpace r s I b) c)
        (fun l => chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l)
        Finset.univ
    exact hmap.symm
  rw [hsplit_output]
  rw [smul_sub, smul_add]

example (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, TensorRSSpace 1 2 I b)
    (X : Π b : M, TangentSpace I b) (b : M) :
    TensorRSSpace 1 2 I b :=
  chartTensorRSCovariantDerivative (I := I) 1 2 g α T X b

example (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, TensorRSSpace 2 1 I b)
    (X : Π b : M, TangentSpace I b) (b : M) :
    TensorRSSpace 2 1 I b :=
  chartTensorRSCovariantDerivative (I := I) 2 1 g α T X b

example (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b : M, TensorRSSpace 0 0 I b)
    (X : Π b : M, TangentSpace I b) (b : M) :
    TensorRSSpace 0 0 I b :=
  chartTensorRSCovariantDerivative (I := I) 0 0 g α T X b

end Connection
end Integral
end DifferentialGeometry
