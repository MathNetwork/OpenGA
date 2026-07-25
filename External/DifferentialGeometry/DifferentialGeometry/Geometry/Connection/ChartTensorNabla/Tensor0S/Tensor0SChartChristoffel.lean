import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0SNabla
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartLocal
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannian


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative
open Tensor0SBundle

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

noncomputable def tensor0SChartE_section_repr (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) : Tensor0SModel s ℝ E :=
  (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b (T b)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
@[simp] lemma tensor0SChartE_section_repr_apply (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) :
    tensor0SChartE_section_repr (I := I) s α T b =
      (trivializationAt (Tensor0SModel s ℝ E)
          (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b (T b) :=
  rfl

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensor0SChartE_section_repr_add (s : ℕ) (α : M)
    (T₁ T₂ : Π b : M, Tensor0SSpace s I b) :
    tensor0SChartE_section_repr (I := I) s α (T₁ + T₂) =
      tensor0SChartE_section_repr (I := I) s α T₁ +
        tensor0SChartE_section_repr (I := I) s α T₂ := by
  funext b
  unfold tensor0SChartE_section_repr
  change (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        ((T₁ + T₂) b) = _
  change (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        (T₁ b + T₂ b) = _
  exact map_add _ (T₁ b) (T₂ b)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensor0SChartE_section_repr_smul (s : ℕ) (α : M) (c : ℝ)
    (T : Π b : M, Tensor0SSpace s I b) :
    tensor0SChartE_section_repr (I := I) s α (c • T) =
      c • tensor0SChartE_section_repr (I := I) s α T := by
  funext b
  unfold tensor0SChartE_section_repr
  change (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        ((c • T) b) = _
  change (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).continuousLinearMapAt ℝ b
        (c • T b) = _
  exact map_smul _ c (T b)

noncomputable def tensor0SChartFiberFromModel (s : ℕ) (α : M) (b : M) :
    Tensor0SModel s ℝ E →L[ℝ] Tensor0SSpace s I b :=
  (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).symmL ℝ b

noncomputable def tensor0SIntrinsicChartCLM (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) :
    TangentSpace I b →L[ℝ] Tensor0SSpace s I b :=
  (tensor0SChartFiberFromModel (I := I) s α b).comp
    ((fderiv ℝ
        (tensor0SChartE_section_repr (I := I) s α T ∘ (extChartAt I α).symm)
        (extChartAt I α b)).comp
      (trivToE (I := I) α b))

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensor0SIntrinsicChartCLM_apply (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) (v : TangentSpace I b) :
    tensor0SIntrinsicChartCLM (I := I) s α T b v =
      tensor0SChartFiberFromModel (I := I) s α b
        (fderiv ℝ
          (tensor0SChartE_section_repr (I := I) s α T ∘ (extChartAt I α).symm)
          (extChartAt I α b) (trivToE (I := I) α b v)) := by
  classical
  unfold tensor0SIntrinsicChartCLM
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensor0SIntrinsicChartCLM_add_section (s : ℕ) (α : M)
    (T₁ T₂ : Π b : M, Tensor0SSpace s I b) (b : M)
    (h₁ : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) s α T₁ ∘ (extChartAt I α).symm)
      (extChartAt I α b))
    (h₂ : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) s α T₂ ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    tensor0SIntrinsicChartCLM (I := I) s α (T₁ + T₂) b =
      tensor0SIntrinsicChartCLM (I := I) s α T₁ b +
        tensor0SIntrinsicChartCLM (I := I) s α T₂ b := by
  classical
  have hsum_pull :
      (tensor0SChartE_section_repr (I := I) s α (T₁ + T₂) ∘
          (extChartAt I α).symm) =
        (tensor0SChartE_section_repr (I := I) s α T₁ ∘
            (extChartAt I α).symm) +
          (tensor0SChartE_section_repr (I := I) s α T₂ ∘
            (extChartAt I α).symm) := by
    funext y
    exact congrFun (tensor0SChartE_section_repr_add (I := I) s α T₁ T₂)
      ((extChartAt I α).symm y)
  have hfd : fderiv ℝ
        (tensor0SChartE_section_repr (I := I) s α (T₁ + T₂) ∘
          (extChartAt I α).symm) (extChartAt I α b) =
      fderiv ℝ
          (tensor0SChartE_section_repr (I := I) s α T₁ ∘
            (extChartAt I α).symm) (extChartAt I α b) +
        fderiv ℝ
          (tensor0SChartE_section_repr (I := I) s α T₂ ∘
            (extChartAt I α).symm) (extChartAt I α b) := by
    rw [hsum_pull]
    exact fderiv_add h₁ h₂
  unfold tensor0SIntrinsicChartCLM
  rw [hfd]
  ext v
  rw [ContinuousLinearMap.add_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.add_apply, map_add]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensor0SIntrinsicChartCLM_smul_section (s : ℕ) (α : M)
    (c : ℝ) (T : Π b : M, Tensor0SSpace s I b) (b : M)
    (hT : DifferentiableAt ℝ
      (tensor0SChartE_section_repr (I := I) s α T ∘ (extChartAt I α).symm)
      (extChartAt I α b)) :
    tensor0SIntrinsicChartCLM (I := I) s α (c • T) b =
      c • tensor0SIntrinsicChartCLM (I := I) s α T b := by
  classical
  have hsmul_pull :
      (tensor0SChartE_section_repr (I := I) s α (c • T) ∘
          (extChartAt I α).symm) =
        c • (tensor0SChartE_section_repr (I := I) s α T ∘
          (extChartAt I α).symm) := by
    funext y
    exact congrFun (tensor0SChartE_section_repr_smul (I := I) s α c T)
      ((extChartAt I α).symm y)
  have hfd : fderiv ℝ
        (tensor0SChartE_section_repr (I := I) s α (c • T) ∘
          (extChartAt I α).symm) (extChartAt I α b) =
      c • fderiv ℝ
          (tensor0SChartE_section_repr (I := I) s α T ∘
            (extChartAt I α).symm) (extChartAt I α b) := by
    rw [hsmul_pull]
    exact fderiv_const_smul hT c
  unfold tensor0SIntrinsicChartCLM
  rw [hfd]
  ext v
  rw [ContinuousLinearMap.smul_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.smul_apply, map_smul]

variable
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

noncomputable def tensor0SChartChristoffelCorrection (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) :
    TangentSpace I b →L[ℝ] Tensor0SSpace s I b :=
  (Tensor0SNabla.tensor0SCovariantDerivative I M s cov T) b -
    tensor0SIntrinsicChartCLM (I := I) s α T b

omit [CompleteSpace E] in
lemma tensor0SChartChristoffelCorrection_def (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) :
    tensor0SChartChristoffelCorrection (I := I) cov s α T b =
      (Tensor0SNabla.tensor0SCovariantDerivative I M s cov T) b -
        tensor0SIntrinsicChartCLM (I := I) s α T b := rfl

omit [CompleteSpace E] in
theorem tensor0SCovariantDerivative_chart_decomp (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) :
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov T) b =
      tensor0SIntrinsicChartCLM (I := I) s α T b +
        tensor0SChartChristoffelCorrection (I := I) cov s α T b := by
  classical
  rw [tensor0SChartChristoffelCorrection_def]
  abel

omit [CompleteSpace E] in
theorem tensor0SCovariantDerivative_chart_decomp_apply (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b) (b : M) (v : TangentSpace I b) :
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov T) b v =
      tensor0SIntrinsicChartCLM (I := I) s α T b v +
        tensor0SChartChristoffelCorrection (I := I) cov s α T b v := by
  classical
  rw [tensor0SCovariantDerivative_chart_decomp (I := I) cov s α T b]
  rw [ContinuousLinearMap.add_apply]

omit [CompleteSpace E] in
theorem tensor0SCovariantDerivative_chart_decomp_vectorField
    (s : ℕ) (α : M)
    (T : Π b : M, Tensor0SSpace s I b)
    (X : Π b : M, TangentSpace I b) (b : M) :
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov T) b (X b) =
      tensor0SIntrinsicChartCLM (I := I) s α T b (X b) +
        tensor0SChartChristoffelCorrection (I := I) cov s α T b (X b) :=
  tensor0SCovariantDerivative_chart_decomp_apply (I := I) cov s α T b (X b)

example
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (s : ℕ) (α : M) (T : Π b : M, Tensor0SSpace s I b) (b : M)
    (v : TangentSpace I b) :
    (Tensor0SNabla.tensor0SCovariantDerivative I M s cov T) b v =
      tensor0SIntrinsicChartCLM (I := I) s α T b v +
        tensor0SChartChristoffelCorrection (I := I) cov s α T b v :=
  tensor0SCovariantDerivative_chart_decomp_apply (I := I) cov s α T b v

end Connection
end Integral
end DifferentialGeometry

end
