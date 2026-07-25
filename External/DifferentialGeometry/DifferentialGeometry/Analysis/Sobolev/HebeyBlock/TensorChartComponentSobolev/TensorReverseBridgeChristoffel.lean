import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentWkpNormBoundFromH1
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.GradNormChartBoundPouWeighted
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorChartComponentSobolevBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceReverse
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.TensorChartComponentSobolev.TensorComponentScalarWkpBound
import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChartParallelTransportOpNorm.ChristoffelCkBound

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma coe_nnnorm_eq_ofReal_norm
    {X : Type*} [SeminormedAddCommGroup X] (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm_eq_enorm x]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponentScalar_eLpNorm_le_h1Norm_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s T.toCcTensor α Idx Jdx) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * ENNReal.ofReal ‖T‖ := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀_bound⟩ :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eLpNorm_le
      (I := I) (M := M) g r s
  refine ⟨C₀, hC₀_nn, ?_⟩
  intro T α Idx Jdx
  have h_bound :=
    hC₀_bound T α Idx Jdx
  have h_coe : (‖T‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖T‖ :=
    coe_nnnorm_eq_ofReal_norm T
  rw [h_coe] at h_bound
  exact h_bound

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponentScalar_wkpNormChart_le_h1Norm_of_grad_l2
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (hGrad : ∃ C_grad : ℝ, 0 ≤ C_grad ∧
      ∀ (T : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (fun b : M => Real.sqrt
            (g.inner b
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s T.toCcTensor α Idx Jdx) b)
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s T.toCcTensor α Idx Jdx) b))) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C_grad * ENNReal.ofReal ‖T‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s T.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal C * ENNReal.ofReal ‖T‖ := by
  classical
  obtain ⟨C_grad, hC_grad_nn, hGrad_le⟩ := hGrad
  have hGrad_le' : ∀ (T : SmoothCcTensorH1 g r s) (α : M)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      eLpNorm (fun b : M => Real.sqrt
          (g.inner b
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s T.toCcTensor α Idx Jdx) b)
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s T.toCcTensor α Idx Jdx) b))) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C_grad * (‖T‖₊ : ℝ≥0∞) := by
    intro T α Idx Jdx
    have h := hGrad_le T α Idx Jdx
    rw [coe_nnnorm_eq_ofReal_norm T]
    exact h
  have hper_α : ∀ α : M, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s T.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal C * (‖T‖₊ : ℝ≥0∞) := by
    intro α
    exact
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_wkpNormChart_le_const_mul_h1Norm
        (I := I) (M := M) g r s α hC_grad_nn
        (fun T Idx Jdx => hGrad_le' T α Idx Jdx)
  set S : Finset M := chartAtlasPOU_activeFinset (I := I) (M := M)
    with hS_def
  set Cα : M → ℝ := fun α => Classical.choose (hper_α α) with hCα_def
  have hCα_nn : ∀ α : M, 0 ≤ Cα α :=
    fun α => (Classical.choose_spec (hper_α α)).1
  have hCα_le : ∀ (α : M) (T : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      wkpNormChart (I := I) (M := M) g 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s T.toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal (Cα α) * (‖T‖₊ : ℝ≥0∞) :=
    fun α T Idx Jdx => (Classical.choose_spec (hper_α α)).2 T Idx Jdx
  refine ⟨∑ α ∈ S, Cα α, Finset.sum_nonneg (fun α _ => hCα_nn α), ?_⟩
  intro T α Idx Jdx
  by_cases hα : α ∈ S
  · have h_per := hCα_le α T Idx Jdx
    have hCα_le_total : Cα α ≤ ∑ β ∈ S, Cα β := by
      have h_split :
          ∑ β ∈ S, Cα β =
            Cα α + ∑ β ∈ S.erase α, Cα β := by
        rw [← Finset.sum_erase_add _ _ hα, add_comm]
      rw [h_split]
      have h_rest_nn : 0 ≤ ∑ β ∈ S.erase α, Cα β :=
        Finset.sum_nonneg (fun β _ => hCα_nn β)
      linarith
    have h_const_le :
        ENNReal.ofReal (Cα α) ≤ ENNReal.ofReal (∑ α ∈ S, Cα α) :=
      ENNReal.ofReal_le_ofReal hCα_le_total
    have h_envelope :
        ENNReal.ofReal (Cα α) * (‖T‖₊ : ℝ≥0∞) ≤
          ENNReal.ofReal (∑ α ∈ S, Cα α) * (‖T‖₊ : ℝ≥0∞) :=
      mul_le_mul_of_nonneg_right h_const_le (zero_le _)
    have h_coe : (‖T‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖T‖ :=
      coe_nnnorm_eq_ofReal_norm T
    rw [h_coe] at h_per h_envelope
    exact h_per.trans h_envelope
  · have h_zero :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartAtlasPOU_eq_zero_of_notMem_activeFinset
        (I := I) (M := M) hα
    have h_scalar_zero :
        tensorChartComponentScalar (I := I) (M := M)
            g r s T.toCcTensor α Idx Jdx = 0 :=
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_eq_zero_of_pou_zero
        (I := I) (M := M) g r s α h_zero T.toCcTensor Idx Jdx
    rw [h_scalar_zero]
    have h_wkp_zero :
        wkpNormChart (I := I) (M := M) g 1 2
            (fun _ : M => (0 : ℝ)) = 0 :=
      wkpNormChart_zero_fun (I := I) (M := M) g (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h_zero_fun_eq :
        (0 : M → ℝ) = (fun _ : M => (0 : ℝ)) := by rfl
    rw [h_zero_fun_eq, h_wkp_zero]
    exact zero_le _

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry

end
