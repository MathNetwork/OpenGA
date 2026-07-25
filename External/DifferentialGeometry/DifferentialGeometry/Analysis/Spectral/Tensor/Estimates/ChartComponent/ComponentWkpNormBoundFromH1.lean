import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBoundFromH1
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.WeakPartial.ComponentSobolevBoundDerivBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.WeakPartial.PartialL2BoundFromH1
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.WeakPartial.ChosenWeakPartialFderivBridge
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceReverse
import DifferentialGeometry.Analysis.Sobolev.Chart.AtlasNorm.AtlasIndependence

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

private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponentScalar_wkpNormChart_le_const_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    {C_grad : ℝ} (hC_grad_nn : 0 ≤ C_grad)
    (hC_grad_bound : ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (fun x : M => Real.sqrt
            (g.inner x
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) x)
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) x))) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C_grad * (‖S‖₊ : ℝ≥0∞)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        wkpNormChart (I := I) (M := M) g 1 2
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  obtain ⟨C_L2, hC_L2_nn, h_L2⟩ :=
    tensorChartComponentScalar_eLpNorm_le_uniform
      (I := I) (M := M) (E := E) g r s α
  have h_L2_apply : ∀ (S : SmoothCcTensorH1 g r s)
      (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C_L2 * (‖S‖₊ : ℝ≥0∞) := by
    intro S Idx Jdx
    have hB := h_L2 S.toCcTensor Idx Jdx
    have h_eq :
        ENNReal.ofReal
            (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) =
          (‖S.toCcTensor‖₊ : ℝ≥0∞) := by
      have h_norm_eq :
          ‖S.toCcTensor‖ = tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun :=
        SmoothCcTensor.norm_def (I := I) (M := M) S.toCcTensor
      rw [show ((‖S.toCcTensor‖₊ : ℝ≥0∞)) = ‖S.toCcTensor‖ₑ from
        (enorm_eq_nnnorm _).symm, ← ofReal_norm_eq_enorm _, h_norm_eq]
    have h_l2_le_h1 : (‖S.toCcTensor‖₊ : ℝ≥0∞) ≤ (‖S‖₊ : ℝ≥0∞) := by
      have h_real : ‖S.toCcTensor‖ ≤ ‖S‖ :=
        SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S
      have h_nnreal : ‖S.toCcTensor‖₊ ≤ ‖S‖₊ := h_real
      exact_mod_cast h_nnreal
    rw [h_eq] at hB
    exact hB.trans (mul_le_mul_of_nonneg_left h_l2_le_h1 (by exact zero_le _))
  have hper_β : ∀ β : M, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 2
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
              (tensorChartComponentScalar (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx))
            (chartTargetEuclid (I := I) (M := M) β) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
    intro β
    obtain ⟨C₀, hC₀_nn, hC₀_le⟩ :=
      eLpNorm_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm
        (I := I) (M := M) g r s α β
    obtain ⟨C_env, hC_env_nn, h_env⟩ :=
      DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.eLpNorm_fderiv_chartSmoothExt_apply_le_const_mul
        (I := I) (M := M) g β (p := (2 : ℝ≥0∞)) hp_one hp_top
    have hper_k : ∀ k : Fin (Module.finrank ℝ E),
        ∀ (S : SmoothCcTensorH1 g r s)
          (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 k
                (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                  (tensorChartComponentScalar (I := I) (M := M)
                    g r s S.toCcTensor α Idx Jdx))
                (chartTargetEuclid (I := I) (M := M) β)) 2
              (volume.restrict (chartTargetEuclid (I := I) (M := M) β)) ≤
            ENNReal.ofReal (C_env * (C_L2 + C_grad)) * (‖S‖₊ : ℝ≥0∞) := by
      intro k S Idx Jdx
      set u : M → ℝ :=
        tensorChartComponentScalar (I := I) (M := M)
          g r s S.toCcTensor α Idx Jdx with hu_def
      set μM : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
      set μE : Measure (EuclN E) :=
        (volume : Measure (EuclN E)).restrict (chartTargetEuclid (I := I) (M := M) β)
      set NS : ℝ≥0∞ := (‖S‖₊ : ℝ≥0∞)
      set gradNorm : M → ℝ := fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
          (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))
      have hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u :=
        tensorChartComponentScalar_contMDiff
          (I := I) (M := M) g r s S.toCcTensor α Idx Jdx
      have h_bridge :=
        eLpNorm_chosenWeakPartial'_chartPushed_eq_eLpNorm_fderiv_chartSmoothExt
          (I := I) (M := M) (α := β) (u := u) hu_smooth k
      have h_env_apply := h_env hu_smooth k
      have h_u_L2 : eLpNorm u 2 μM ≤ ENNReal.ofReal C_L2 * NS :=
        h_L2_apply S Idx Jdx
      have h_grad : eLpNorm gradNorm 2 μM ≤ ENNReal.ofReal C_grad * NS :=
        hC_grad_bound S Idx Jdx
      have h_inner_sum :
          eLpNorm u 2 μM + eLpNorm gradNorm 2 μM ≤
            ENNReal.ofReal C_L2 * NS + ENNReal.ofReal C_grad * NS :=
        add_le_add h_u_L2 h_grad
      have hMain :
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 k
                (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u)
                (chartTargetEuclid (I := I) (M := M) β)) 2 μE ≤
            ENNReal.ofReal (C_env * (C_L2 + C_grad)) * NS := by
        rw [h_bridge]
        refine h_env_apply.trans ?_
        calc ENNReal.ofReal C_env *
                (eLpNorm u 2 μM + eLpNorm gradNorm 2 μM)
            ≤ ENNReal.ofReal C_env *
                  (ENNReal.ofReal C_L2 * NS + ENNReal.ofReal C_grad * NS) :=
              mul_le_mul_of_nonneg_left h_inner_sum (by exact zero_le _)
          _ = ENNReal.ofReal C_env *
                  ((ENNReal.ofReal C_L2 + ENNReal.ofReal C_grad) * NS) := by
              rw [← add_mul]
          _ = ENNReal.ofReal C_env * (ENNReal.ofReal (C_L2 + C_grad) * NS) := by
              rw [(ENNReal.ofReal_add hC_L2_nn hC_grad_nn).symm]
          _ = (ENNReal.ofReal C_env * ENNReal.ofReal (C_L2 + C_grad)) * NS := by
              rw [← mul_assoc]
          _ = ENNReal.ofReal (C_env * (C_L2 + C_grad)) * NS := by
              rw [(ENNReal.ofReal_mul hC_env_nn).symm]
      rw [hu_def] at hMain
      exact hMain
    set N : ℕ := Fintype.card (Fin (Module.finrank ℝ E))
    refine ⟨C₀ + (N : ℝ) * (C_env * (C_L2 + C_grad)),
      add_nonneg hC₀_nn (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg hC_env_nn (add_nonneg hC_L2_nn hC_grad_nn))), ?_⟩
    intro S Idx Jdx
    set u : EuclN E → ℝ :=
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
        (tensorChartComponentScalar (I := I) (M := M)
          g r s S.toCcTensor α Idx Jdx) with hu_def
    set Ω : Set (EuclN E) := chartTargetEuclid (I := I) (M := M) β with hΩ_def
    rw [wkpNorm_one_two_decomposition (E := E) u Ω]
    have h0 : eLpNorm u 2 (volume.restrict Ω) ≤
        ENNReal.ofReal C₀ * (‖S‖₊ : ℝ≥0∞) := by
      rw [hu_def, hΩ_def]; exact hC₀_le S Idx Jdx
    have h1 : ∑ k : Fin (Module.finrank ℝ E),
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                (d := Module.finrank ℝ E) 2 k u Ω) 2
              (volume.restrict Ω) ≤
        (N : ℝ≥0∞) * (ENNReal.ofReal (C_env * (C_L2 + C_grad)) *
          (‖S‖₊ : ℝ≥0∞)) := by
      rw [hu_def, hΩ_def]
      calc ∑ k : Fin (Module.finrank ℝ E),
              eLpNorm
                (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
                  (d := Module.finrank ℝ E) 2 k
                  (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β
                    (tensorChartComponentScalar (I := I) (M := M)
                      g r s S.toCcTensor α Idx Jdx))
                  (chartTargetEuclid (I := I) (M := M) β)) 2
                (volume.restrict (chartTargetEuclid (I := I) (M := M) β))
          ≤ ∑ _k : Fin (Module.finrank ℝ E),
                ENNReal.ofReal (C_env * (C_L2 + C_grad)) * (‖S‖₊ : ℝ≥0∞) :=
              Finset.sum_le_sum (fun k _ => hper_k k S Idx Jdx)
        _ = (N : ℝ≥0∞) * (ENNReal.ofReal (C_env * (C_L2 + C_grad)) *
              (‖S‖₊ : ℝ≥0∞)) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    refine (add_le_add h0 h1).trans ?_
    have hN_ofReal : (N : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) := by
      rw [ENNReal.ofReal_natCast]
    have hC_env_total_nn : 0 ≤ C_env * (C_L2 + C_grad) :=
      mul_nonneg hC_env_nn (add_nonneg hC_L2_nn hC_grad_nn)
    rw [hN_ofReal]
    refine le_of_eq ?_
    calc ENNReal.ofReal C₀ * (‖S‖₊ : ℝ≥0∞) +
            ENNReal.ofReal (N : ℝ) *
              (ENNReal.ofReal (C_env * (C_L2 + C_grad)) * (‖S‖₊ : ℝ≥0∞))
        = ENNReal.ofReal C₀ * (‖S‖₊ : ℝ≥0∞) +
            (ENNReal.ofReal (N : ℝ) * ENNReal.ofReal (C_env * (C_L2 + C_grad))) *
              (‖S‖₊ : ℝ≥0∞) := by rw [mul_assoc]
      _ = ENNReal.ofReal C₀ * (‖S‖₊ : ℝ≥0∞) +
            ENNReal.ofReal ((N : ℝ) * (C_env * (C_L2 + C_grad))) *
              (‖S‖₊ : ℝ≥0∞) := by
            rw [(ENNReal.ofReal_mul (Nat.cast_nonneg _)).symm]
      _ = (ENNReal.ofReal C₀ +
            ENNReal.ofReal ((N : ℝ) * (C_env * (C_L2 + C_grad)))) *
              (‖S‖₊ : ℝ≥0∞) := by rw [← add_mul]
      _ = ENNReal.ofReal (C₀ + (N : ℝ) * (C_env * (C_L2 + C_grad))) *
              (‖S‖₊ : ℝ≥0∞) := by
            rw [(ENNReal.ofReal_add hC₀_nn
              (mul_nonneg (Nat.cast_nonneg _) hC_env_total_nn)).symm]
  set finS : Finset M := chartAtlasPOU_finset (I := I) (M := M) with hfinS_def
  choose Cβ hCβ_nn hCβ_le using hper_β
  refine ⟨∑ β ∈ finS, Cβ β, Finset.sum_nonneg (fun β _ => hCβ_nn β), ?_⟩
  intro S Idx Jdx
  set u : M → ℝ :=
    tensorChartComponentScalar (I := I) (M := M)
      g r s S.toCcTensor α Idx Jdx with hu_def
  have h_def : wkpNormChart (I := I) (M := M) g 1 2 u =
      ∑' β : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u)
          (chartTargetEuclid (I := I) (M := M) β) := rfl
  rw [h_def]
  have h_outside_zero : ∀ β : M, β ∉ finS →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u)
        (chartTargetEuclid (I := I) (M := M) β) = 0 := by
    intro β hβ
    have hβ' : β ∉ chartAtlasPOU_finset (I := I) (M := M) := by
      rw [hfinS_def] at hβ; exact hβ
    have hρ_zero : ∀ x : M,
        ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 :=
      fun x => DifferentialGeometry.Integral.Measure.chartAtlasPOU_weight_zero_of_notMem
        (I := I) (M := M) hβ' x
    exact wkpNorm_chartPushed_eq_zero_of_pou_zero
      (I := I) (M := M) hp_one
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) β u hρ_zero
  rw [tsum_eq_sum (s := finS) h_outside_zero]
  have h_per_β : ∀ β ∈ finS,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) β u)
        (chartTargetEuclid (I := I) (M := M) β) ≤
      ENNReal.ofReal (Cβ β) * (‖S‖₊ : ℝ≥0∞) := by
    intro β _; rw [hu_def]; exact hCβ_le β S Idx Jdx
  refine (Finset.sum_le_sum h_per_β).trans ?_
  rw [← Finset.sum_mul]
  gcongr
  rw [show (∑ β ∈ finS, ENNReal.ofReal (Cβ β)) =
        ENNReal.ofReal (∑ β ∈ finS, Cβ β) from
    (ENNReal.ofReal_sum_of_nonneg (fun β _ => hCβ_nn β)).symm]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
