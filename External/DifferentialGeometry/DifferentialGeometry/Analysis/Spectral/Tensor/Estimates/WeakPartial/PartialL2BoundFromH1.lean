import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.WeakPartial.ChosenWeakPartialFderivBridge
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBoundFromH1
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceReverse

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private abbrev EuclN (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_eLpNorm_tensorChartComponentScalar_le_const_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C₂, hC₂_nn, h_man⟩ :=
    tensorChartComponentScalar_eLpNorm_le_uniform
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C₂, hC₂_nn, ?_⟩
  intro S Idx Jdx
  have hB :
      eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C₂ *
          ENNReal.ofReal
            (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) :=
    h_man S.toCcTensor Idx Jdx
  have h_eq :
      ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) =
        (‖S.toCcTensor‖₊ : ℝ≥0∞) := by
    have h_norm_eq :
        ‖S.toCcTensor‖ = tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun :=
      rfl
    have h_nnnorm_ofReal :
        (‖S.toCcTensor‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖S.toCcTensor‖ := by
      rw [show ((‖S.toCcTensor‖₊ : ℝ≥0∞)) = ‖S.toCcTensor‖ₑ from
        (enorm_eq_nnnorm _).symm, ← ofReal_norm_eq_enorm _]
    rw [h_nnnorm_ofReal, h_norm_eq]
  rw [h_eq] at hB
  have h_l2_le_h1 :
      (‖S.toCcTensor‖₊ : ℝ≥0∞) ≤ (‖S‖₊ : ℝ≥0∞) := by
    have h_real : ‖S.toCcTensor‖ ≤ ‖S‖ :=
      SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S
    have h_nnreal : ‖S.toCcTensor‖₊ ≤ ‖S‖₊ := h_real
    exact_mod_cast h_nnreal
  have hB' :
      eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx) 2
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C₂ * (‖S‖₊ : ℝ≥0∞) :=
    hB.trans (mul_le_mul_of_nonneg_left h_l2_le_h1 (by exact zero_le _))
  exact hB'

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_eLpNorm_chosenWeakPartial'_chartPushed_tensorChartComponentScalar_le_const_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (k : Fin (Module.finrank ℝ E))
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
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) α)) 2
            (volume.restrict (chartTargetEuclid (I := I) (M := M) α)) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  obtain ⟨C_env, hC_env_nn, h_env⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.eLpNorm_fderiv_chartSmoothExt_apply_le_const_mul
      (I := I) (M := M) g α (p := (2 : ℝ≥0∞)) hp_one hp_top
  obtain ⟨C_L2, hC_L2_nn, h_L2⟩ :=
    exists_eLpNorm_tensorChartComponentScalar_le_const_mul_h1Norm
      (I := I) (M := M) g r s α
  refine ⟨C_env * (C_L2 + C_grad),
    mul_nonneg hC_env_nn (add_nonneg hC_L2_nn hC_grad_nn), ?_⟩
  intro S Idx Jdx
  set u : M → ℝ :=
    tensorChartComponentScalar (I := I) (M := M)
      g r s S.toCcTensor α Idx Jdx with hu_def
  set μM : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμM_def
  set μE : Measure (EuclN E) :=
    (volume : Measure (EuclN E)).restrict
      (chartTargetEuclid (I := I) (M := M) α) with hμE_def
  set NS : ℝ≥0∞ := (‖S‖₊ : ℝ≥0∞) with hNS_def
  have hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u := by
    rw [hu_def]
    exact tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s S.toCcTensor α Idx Jdx
  have h_bridge :
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 k
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α)) 2 μE =
        eLpNorm
          (fun y : EuclN E => fderiv ℝ
            (chartSmoothExt (I := I) (M := M) α
              (fun z : M => ((chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
              (EuclideanSpace.single k (1 : ℝ))) 2 μE :=
    eLpNorm_chosenWeakPartial'_chartPushed_eq_eLpNorm_fderiv_chartSmoothExt
      (I := I) (M := M) (α := α) (u := u) hu_smooth k
  have h_env_apply :
      eLpNorm
          (fun y : EuclN E => fderiv ℝ
            (chartSmoothExt (I := I) (M := M) α
              (fun z : M => ((chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
              (EuclideanSpace.single k (1 : ℝ))) 2 μE ≤
        ENNReal.ofReal C_env *
          (eLpNorm u 2 μM +
            eLpNorm (fun x : M => Real.sqrt
                (g.inner x
                  (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
                  (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) 2 μM) :=
    h_env hu_smooth k
  have h_L2_apply :
      eLpNorm u 2 μM ≤ ENNReal.ofReal C_L2 * NS := by
    rw [hu_def, hμM_def, hNS_def]
    exact h_L2 S Idx Jdx
  have h_grad_apply :
      eLpNorm (fun x : M => Real.sqrt
          (g.inner x
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
            (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) 2 μM ≤
        ENNReal.ofReal C_grad * NS := by
    rw [hu_def, hμM_def, hNS_def]
    exact hC_grad_bound S Idx Jdx
  have h_inner_sum :
      eLpNorm u 2 μM +
        eLpNorm (fun x : M => Real.sqrt
            (g.inner x
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
              (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) 2 μM ≤
        ENNReal.ofReal C_L2 * NS + ENNReal.ofReal C_grad * NS :=
    add_le_add h_L2_apply h_grad_apply
  have h_factor_sum :
      ENNReal.ofReal C_L2 * NS + ENNReal.ofReal C_grad * NS =
        (ENNReal.ofReal C_L2 + ENNReal.ofReal C_grad) * NS := by
    rw [← add_mul]
  have h_ofReal_add :
      ENNReal.ofReal C_L2 + ENNReal.ofReal C_grad =
        ENNReal.ofReal (C_L2 + C_grad) :=
    (ENNReal.ofReal_add hC_L2_nn hC_grad_nn).symm
  have h_main :
      eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
            (d := Module.finrank ℝ E) 2 k
            (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α)) 2 μE ≤
        ENNReal.ofReal C_env * (ENNReal.ofReal (C_L2 + C_grad) * NS) := by
    calc eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 k
              (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α u)
              (chartTargetEuclid (I := I) (M := M) α)) 2 μE
        = eLpNorm
            (fun y : EuclN E => fderiv ℝ
              (chartSmoothExt (I := I) (M := M) α
                (fun z : M => ((chartAtlasPOU I M α
                  : C^∞⟮I, M; ℝ⟯) : M → ℝ) z * u z)) y
                (EuclideanSpace.single k (1 : ℝ))) 2 μE := h_bridge
      _ ≤ ENNReal.ofReal C_env *
            (eLpNorm u 2 μM +
              eLpNorm (fun x : M => Real.sqrt
                  (g.inner x
                    (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x)
                    (DifferentialGeometry.Integral.DivergenceTheorem.gradFun (I := I) g u x))) 2 μM) :=
          h_env_apply
      _ ≤ ENNReal.ofReal C_env *
            (ENNReal.ofReal C_L2 * NS + ENNReal.ofReal C_grad * NS) :=
          mul_le_mul_of_nonneg_left h_inner_sum (by exact zero_le _)
      _ = ENNReal.ofReal C_env *
            ((ENNReal.ofReal C_L2 + ENNReal.ofReal C_grad) * NS) := by
          rw [h_factor_sum]
      _ = ENNReal.ofReal C_env *
            (ENNReal.ofReal (C_L2 + C_grad) * NS) := by
          rw [h_ofReal_add]
  have h_C_sum_nn : 0 ≤ C_L2 + C_grad := add_nonneg hC_L2_nn hC_grad_nn
  have h_C_prod_eq :
      ENNReal.ofReal C_env * ENNReal.ofReal (C_L2 + C_grad) =
        ENNReal.ofReal (C_env * (C_L2 + C_grad)) :=
    (ENNReal.ofReal_mul hC_env_nn).symm
  rw [hu_def] at h_main
  have h_final_form :
      ENNReal.ofReal C_env * (ENNReal.ofReal (C_L2 + C_grad) * NS) =
        ENNReal.ofReal (C_env * (C_L2 + C_grad)) * NS := by
    rw [← mul_assoc, h_C_prod_eq]
  rw [h_final_form] at h_main
  exact h_main

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
