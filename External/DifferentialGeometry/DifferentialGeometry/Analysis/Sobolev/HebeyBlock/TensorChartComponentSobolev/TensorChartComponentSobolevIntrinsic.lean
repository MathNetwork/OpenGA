import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.TensorChartComponentSobolev.PerAlphaGradIntrinsic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace HebeyBlock

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [CompleteSpace E] in
private lemma exists_perAlphaSobolevConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C_grad, hC_grad_nn, hC_grad_bound⟩ :=
    tensorChartComponentScalar_grad_eLpNorm_le
      (I := I) (M := M) g r s
  exact tensorChartComponentScalar_wkpNormChart_le_const_mul_h1Norm
    (I := I) (M := M) g r s α hC_grad_nn
    (fun S Idx Jdx => hC_grad_bound S α Idx Jdx)

private noncomputable def perAlphaSobolevConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) : ℝ :=
  Classical.choose
    (exists_perAlphaSobolevConstant (I := I) (M := M) g r s α)

omit [CompleteSpace E] in
private lemma perAlphaSobolevConstant_intrinsic_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    0 ≤ perAlphaSobolevConstant (I := I) (M := M) g r s α :=
  (Classical.choose_spec
    (exists_perAlphaSobolevConstant
      (I := I) (M := M) g r s α)).1

omit [CompleteSpace E] in
private lemma perAlphaSobolevConstant_intrinsic_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    wkpNormChart (I := I) (M := M) g 1 2
        (tensorChartComponentScalar (I := I) (M := M)
          g r s S.toCcTensor α Idx Jdx) ≤
      ENNReal.ofReal
          (perAlphaSobolevConstant (I := I) (M := M) g r s α) *
        (‖S‖₊ : ℝ≥0∞) :=
  (Classical.choose_spec
    (exists_perAlphaSobolevConstant
      (I := I) (M := M) g r s α)).2 S Idx Jdx

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma wkpNormChart_tensorChartComponentScalar_eq_zero_of_inactive_intrinsic
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    wkpNormChart (I := I) (M := M) g 1 2
        (tensorChartComponentScalar (I := I) (M := M)
          g r s S α Idx Jdx) = 0 := by
  have h_zero :=
    chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
  have h_scalar_zero :
      tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx = 0 :=
    tensorChartComponentScalar_eq_zero_of_pou_zero
      (I := I) (M := M) g r s α h_zero S Idx Jdx
  rw [h_scalar_zero]
  exact wkpNormChart_zero_fun (I := I) (M := M) g (by norm_num : (1 : ℝ≥0∞) ≤ 2)

private noncomputable def totalActiveSobolevConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) : ℝ :=
  ∑ α ∈ chartAtlasPOU_activeFinset I M,
    perAlphaSobolevConstant (I := I) (M := M) g r s α

omit [CompleteSpace E] in
private lemma totalActiveSobolevConstant_intrinsic_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    0 ≤ totalActiveSobolevConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActiveSobolevConstant
  exact Finset.sum_nonneg (fun α _ =>
    perAlphaSobolevConstant_intrinsic_nonneg (I := I) (M := M) g r s α)

omit [CompleteSpace E] in
private lemma perAlphaSobolevConstant_le_totalActiveSobolevConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {α : M}
    (hα : α ∈ chartAtlasPOU_activeFinset I M) :
    perAlphaSobolevConstant (I := I) (M := M) g r s α ≤
      totalActiveSobolevConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActiveSobolevConstant
  have h_split :
      ∑ β ∈ chartAtlasPOU_activeFinset I M,
        perAlphaSobolevConstant (I := I) (M := M) g r s β =
        perAlphaSobolevConstant (I := I) (M := M) g r s α +
        ∑ β ∈ (chartAtlasPOU_activeFinset I M).erase α,
          perAlphaSobolevConstant (I := I) (M := M) g r s β := by
    rw [← Finset.sum_erase_add _ _ hα, add_comm]
  rw [h_split]
  have h_rest_nn :
      0 ≤ ∑ β ∈ (chartAtlasPOU_activeFinset I M).erase α,
            perAlphaSobolevConstant (I := I) (M := M) g r s β :=
    Finset.sum_nonneg (fun β _ =>
      perAlphaSobolevConstant_intrinsic_nonneg (I := I) (M := M) g r s β)
  linarith

omit [CompleteSpace E] in
theorem tensorChartComponent_wkpNormChart_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  refine ⟨totalActiveSobolevConstant (I := I) (M := M) g r s,
    totalActiveSobolevConstant_intrinsic_nonneg (I := I) (M := M) g r s, ?_⟩
  intro S α Idx Jdx
  by_cases hα : α ∈ chartAtlasPOU_activeFinset I M
  · have h_per :
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal
              (perAlphaSobolevConstant (I := I) (M := M) g r s α) *
            (‖S‖₊ : ℝ≥0∞) :=
      perAlphaSobolevConstant_intrinsic_bound
        (I := I) (M := M) g r s α S Idx Jdx
    have h_const_le :
        ENNReal.ofReal
            (perAlphaSobolevConstant (I := I) (M := M) g r s α) ≤
          ENNReal.ofReal
            (totalActiveSobolevConstant (I := I) (M := M) g r s) :=
      ENNReal.ofReal_le_ofReal
        (perAlphaSobolevConstant_le_totalActiveSobolevConstant
          (I := I) (M := M) g r s hα)
    have h_envelope_le :
        ENNReal.ofReal
              (perAlphaSobolevConstant (I := I) (M := M) g r s α) *
              (‖S‖₊ : ℝ≥0∞) ≤
          ENNReal.ofReal
              (totalActiveSobolevConstant (I := I) (M := M) g r s) *
              (‖S‖₊ : ℝ≥0∞) :=
      mul_le_mul_of_nonneg_right h_const_le (by exact zero_le _)
    exact h_per.trans h_envelope_le
  · rw [wkpNormChart_tensorChartComponentScalar_eq_zero_of_inactive_intrinsic
      (I := I) (M := M) g r s hα S.toCcTensor Idx Jdx]
    exact zero_le _

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry

end
