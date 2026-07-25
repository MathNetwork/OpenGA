import DifferentialGeometry.Analysis.Sobolev.HebeyBlock.TensorChartComponentSobolev.PerChartGradientL2Headline
import DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorChartComponentSobolevBound


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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma eLpNorm_sqrt_g_inner_gradFun_eq_zero_of_inactive_intrinsic
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {α : M} (hα : α ∉ chartAtlasPOU_activeFinset I M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    eLpNorm (fun b : M => Real.sqrt
        (g.inner b
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) b)
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S α Idx Jdx) b))) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  classical
  have h_zero :=
    chartAtlasPOU_eq_zero_of_notMem_activeFinset (I := I) (M := M) hα
  have h_scalar_zero :
      tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx = 0 :=
    tensorChartComponentScalar_eq_zero_of_pou_zero
      (I := I) (M := M) g r s α h_zero S Idx Jdx
  have h_integrand_zero :
      (fun b : M => Real.sqrt
          (g.inner b
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx) b)
            (gradFun (I := I) g
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S α Idx Jdx) b))) = 0 := by
    funext b
    have h_ev :
        (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx)
          =ᶠ[𝓝 b] (fun _ : M => (0 : ℝ)) := by
      rw [h_scalar_zero]; rfl
    have h_grad_zero :
        gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) b =
          (0 : TangentSpace I b) :=
      gradFun_eq_zero_of_eventuallyEq_zero (I := I) g h_ev
    rw [h_grad_zero]
    have h_map : g.inner b (0 : TangentSpace I b) =
        (0 : TangentSpace I b →L[ℝ] ℝ) := map_zero _
    rw [h_map]
    change Real.sqrt ((0 : TangentSpace I b →L[ℝ] ℝ) (0 : TangentSpace I b)) =
      (0 : M → ℝ) b
    simp
  rw [h_integrand_zero]
  exact eLpNorm_zero

private noncomputable def perAlphaGradConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) : ℝ :=
  Classical.choose
    (exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
      (I := I) (M := M) g r s α)

omit [CompleteSpace E] in
private lemma perAlphaGradConstant_intrinsic_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    0 ≤ perAlphaGradConstant (I := I) (M := M) g r s α :=
  (Classical.choose_spec
    (exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
      (I := I) (M := M) g r s α)).1

omit [CompleteSpace E] in
private lemma perAlphaGradConstant_intrinsic_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    eLpNorm (fun b : M => Real.sqrt
        (g.inner b
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) b)
          (gradFun (I := I) g
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) b))) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
      ENNReal.ofReal (perAlphaGradConstant (I := I) (M := M) g r s α) *
        (‖S‖₊ : ℝ≥0∞) :=
  (Classical.choose_spec
    (exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
      (I := I) (M := M) g r s α)).2 S Idx Jdx

private noncomputable def totalActiveGradConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) : ℝ :=
  ∑ α ∈ chartAtlasPOU_activeFinset I M,
    perAlphaGradConstant (I := I) (M := M) g r s α

omit [CompleteSpace E] in
private lemma totalActiveGradConstant_intrinsic_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    0 ≤ totalActiveGradConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActiveGradConstant
  exact Finset.sum_nonneg (fun α _ =>
    perAlphaGradConstant_intrinsic_nonneg (I := I) (M := M) g r s α)

omit [CompleteSpace E] in
private lemma perAlphaGradConstant_le_totalActiveGradConstant
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {α : M}
    (hα : α ∈ chartAtlasPOU_activeFinset I M) :
    perAlphaGradConstant (I := I) (M := M) g r s α ≤
      totalActiveGradConstant (I := I) (M := M) g r s := by
  classical
  unfold totalActiveGradConstant
  have h_split :
      ∑ β ∈ chartAtlasPOU_activeFinset I M,
        perAlphaGradConstant (I := I) (M := M) g r s β =
        perAlphaGradConstant (I := I) (M := M) g r s α +
        ∑ β ∈ (chartAtlasPOU_activeFinset I M).erase α,
          perAlphaGradConstant (I := I) (M := M) g r s β := by
    rw [← Finset.sum_erase_add _ _ hα, add_comm]
  rw [h_split]
  have h_rest_nn :
      0 ≤ ∑ β ∈ (chartAtlasPOU_activeFinset I M).erase α,
            perAlphaGradConstant (I := I) (M := M) g r s β :=
    Finset.sum_nonneg (fun β _ =>
      perAlphaGradConstant_intrinsic_nonneg (I := I) (M := M) g r s β)
  linarith

omit [CompleteSpace E] in
theorem tensorChartComponentScalar_grad_eLpNorm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C_grad : ℝ, 0 ≤ C_grad ∧
      ∀ (S : SmoothCcTensorH1 g r s) (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (fun b : M => Real.sqrt
            (g.inner b
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b)
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b))) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C_grad * (‖S‖₊ : ℝ≥0∞) := by
  classical
  refine ⟨totalActiveGradConstant (I := I) (M := M) g r s,
    totalActiveGradConstant_intrinsic_nonneg (I := I) (M := M) g r s, ?_⟩
  intro S α Idx Jdx
  by_cases hα : α ∈ chartAtlasPOU_activeFinset I M
  · have h_per :
        eLpNorm (fun b : M => Real.sqrt
            (g.inner b
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b)
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b))) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal
              (perAlphaGradConstant (I := I) (M := M) g r s α) *
            (‖S‖₊ : ℝ≥0∞) :=
      perAlphaGradConstant_intrinsic_bound (I := I) (M := M) g r s α S Idx Jdx
    have h_const_le :
        ENNReal.ofReal
            (perAlphaGradConstant (I := I) (M := M) g r s α) ≤
          ENNReal.ofReal
            (totalActiveGradConstant (I := I) (M := M) g r s) :=
      ENNReal.ofReal_le_ofReal
        (perAlphaGradConstant_le_totalActiveGradConstant
          (I := I) (M := M) g r s hα)
    have h_envelope_le :
        ENNReal.ofReal
              (perAlphaGradConstant (I := I) (M := M) g r s α) *
              (‖S‖₊ : ℝ≥0∞) ≤
          ENNReal.ofReal
              (totalActiveGradConstant (I := I) (M := M) g r s) *
              (‖S‖₊ : ℝ≥0∞) :=
      mul_le_mul_of_nonneg_right h_const_le (by exact zero_le _)
    exact h_per.trans h_envelope_le
  · rw [eLpNorm_sqrt_g_inner_gradFun_eq_zero_of_inactive_intrinsic
      (I := I) (M := M) g r s hα S.toCcTensor Idx Jdx]
    exact zero_le _

end HebeyBlock
end RicciFlow
end PDE
end DifferentialGeometry

end
