import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.IntrinsicL2Bridge
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBound
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma abs_pou_mul_le_abs_local
    (β : M) (u : M → ℝ) (x : M) :
    |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x| ≤ |u x| := by
  rw [abs_mul]
  have hρ_nn : 0 ≤ ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg β x
  have hρ_le : ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≤ 1 :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).le_one β x
  have hρ_abs_le_one : |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x| ≤ 1 := by
    rw [abs_of_nonneg hρ_nn]; exact hρ_le
  calc |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x| * |u x|
      ≤ 1 * |u x| := by gcongr
    _ = |u x| := one_mul _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure_uniform
    (g : SmoothRiemannianMetric I M) (β : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : M → ℝ) (_hu_meas : Measurable u),
        eLpNorm
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u) 2
            ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C *
            eLpNorm u 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M β with hρ_def
  set Kβ : Set M := tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKβ_def
  have hKβ_compact : IsCompact Kβ := (isClosed_tsupport _).isCompact
  have hKβ_sub : Kβ ⊆ (chartAt H β).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M β
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by decide
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g β hKβ_compact hKβ_sub hp_one hp_top
  refine ⟨C, hC_pos.le, ?_⟩
  intro u hu_meas
  set f : M → ℝ := fun x : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x with hf_def
  have hρ_cont : Continuous ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    (ρ.contMDiff).continuous
  have hf_meas : Measurable f := hρ_cont.measurable.mul hu_meas
  have hf_supp : tsupport f ⊆ Kβ := by
    have h_eq : f = (fun x : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • u x) := by
      funext x; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun x : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)
  have h_raw_bound := hC_bound (u := f) hf_meas hf_supp
  rw [show DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
        = DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g from rfl]
    at h_raw_bound
  have h_ae :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_ae
      (I := I) (M := M)
      (ρ := DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      β u
  rw [eLpNorm_congr_ae h_ae]
  refine h_raw_bound.trans ?_
  gcongr
  refine eLpNorm_mono (f := f) (g := u) ?_
  intro x
  have h_norm_f : ‖f x‖ = |((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x| := Real.norm_eq_abs _
  have h_norm_u : ‖u x‖ = |u x| := Real.norm_eq_abs _
  rw [h_norm_f, h_norm_u]
  exact abs_pou_mul_le_abs_local (I := I) (M := M) β u x

private lemma coe_nnnorm_eq_ofReal_norm {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm_eq_enorm x]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma ofReal_tensorL2Norm_toFun_eq_nnnorm_toCcTensor
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ENNReal.ofReal (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) =
      (‖S.toCcTensor‖₊ : ℝ≥0∞) := by
  have h_norm_eq :
      ‖S.toCcTensor‖ = tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun :=
    SmoothCcTensor.norm_def (I := I) (M := M) S.toCcTensor
  rw [← h_norm_eq, ← coe_nnnorm_eq_ofReal_norm]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma nnnorm_toCcTensor_le_nnnorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    (‖S.toCcTensor‖₊ : ℝ≥0∞) ≤ (‖S‖₊ : ℝ≥0∞) := by
  have h_real : ‖S.toCcTensor‖ ≤ ‖S‖ :=
    SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S
  rw [coe_nnnorm_eq_ofReal_norm, coe_nnnorm_eq_ofReal_norm]
  exact ENNReal.ofReal_le_ofReal h_real

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α β : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx)) 2
            ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) β)) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C₁, hC₁_nn, hC₁_uniform⟩ :=
    eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure_uniform
      (I := I) (M := M) g β
  obtain ⟨C₂, hC₂_nn, h_man⟩ :=
    tensorChartComponentScalar_eLpNorm_le_uniform
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C₁ * C₂, mul_nonneg hC₁_nn hC₂_nn, ?_⟩
  intro S Idx Jdx
  set u : M → ℝ :=
    tensorChartComponentScalar (I := I) (M := M) g r s S.toCcTensor α Idx Jdx
    with hu_def
  have hu_meas : Measurable u :=
    (tensorChartComponentScalar_contMDiff (I := I) (M := M)
      g r s S.toCcTensor α Idx Jdx).continuous.measurable
  have hA :
      eLpNorm
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u) 2
          ((volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) β)) ≤
        ENNReal.ofReal C₁ *
          eLpNorm u 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hC₁_uniform u hu_meas
  have hB :
      eLpNorm u 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C₂ *
          ENNReal.ofReal
            (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) := by
    rw [hu_def]
    exact h_man S.toCcTensor Idx Jdx
  have hAB :
      eLpNorm
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u) 2
          ((volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (chartTargetEuclid (I := I) (M := M) β)) ≤
        ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun)) := by
    calc eLpNorm
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u) 2
            ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) β))
        ≤ ENNReal.ofReal C₁ *
            eLpNorm u 2 (riemannianVolumeMeasure (I := I) (M := M) g) := hA
      _ ≤ ENNReal.ofReal C₁ *
            (ENNReal.ofReal C₂ *
              ENNReal.ofReal
                (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun)) :=
          mul_le_mul_of_nonneg_left hB (by exact zero_le _)
  have h_eq :
      ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) =
        (‖S.toCcTensor‖₊ : ℝ≥0∞) :=
    ofReal_tensorL2Norm_toFun_eq_nnnorm_toCcTensor
      (I := I) (M := M) g r s S
  have h_le :
      (‖S.toCcTensor‖₊ : ℝ≥0∞) ≤ (‖S‖₊ : ℝ≥0∞) :=
    nnnorm_toCcTensor_le_nnnorm (I := I) (M := M) g r s S
  refine hAB.trans ?_
  rw [h_eq]
  calc ENNReal.ofReal C₁ *
          (ENNReal.ofReal C₂ * (‖S.toCcTensor‖₊ : ℝ≥0∞))
      = (ENNReal.ofReal C₁ * ENNReal.ofReal C₂) *
            (‖S.toCcTensor‖₊ : ℝ≥0∞) := by
        rw [mul_assoc]
    _ = ENNReal.ofReal (C₁ * C₂) * (‖S.toCcTensor‖₊ : ℝ≥0∞) := by
        rw [(ENNReal.ofReal_mul hC₁_nn).symm]
    _ ≤ ENNReal.ofReal (C₁ * C₂) * (‖S‖₊ : ℝ≥0∞) :=
        mul_le_mul_of_nonneg_left h_le (by exact zero_le _)

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm_forall
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α β : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensorH1 g r s,
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          eLpNorm
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)) 2
              ((volume :
                  Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) β)) ≤
            ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) :=
  eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm
    (I := I) (M := M) g r s α β

omit [NeZero (Module.finrank ℝ E)] in
theorem eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm_single_chart
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx)) 2
            ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) :=
  eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm
    (I := I) (M := M) g r s α α

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
