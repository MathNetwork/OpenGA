import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.WeakPartialOnVolume
import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.CLM.ChartFormula
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.ChartData
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartPushedRawWeakPartialOnVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientChartBridge
open DifferentialGeometry.Analysis.Laplacian.H1ComplToLpChartBridge
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

noncomputable def chartPushedRawPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g) : EuclN → ℝ :=
  fun y =>
    (fderiv ℝ (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α v.toFun) y)
      (EuclideanSpace.single j 1)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
@[simp] lemma chartPushedRawPartial_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) (v : SmoothScalar g) (y : EuclN) :
    chartPushedRawPartial (I := I) (M := M) g α j v y =
      (fderiv ℝ (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α v.toFun) y)
        (EuclideanSpace.single j 1) := rfl

structure ChartPushedRawPartialLipschitz
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E)) where

  C : ℝ

  C_nonneg : 0 ≤ C

  memLp : ∀ v : SmoothScalar g,
    MemLp (chartPushedRawPartial (I := I) (M := M) g α j v) 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))

  bound : ∀ v : SmoothScalar g,
    eLpNorm (chartPushedRawPartial (I := I) (M := M) g α j v) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      ENNReal.ofReal C * (‖v‖₊ : ℝ≥0∞)

  add : ∀ v w : SmoothScalar g,
    chartPushedRawPartial (I := I) (M := M) g α j (v + w) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fun y => chartPushedRawPartial (I := I) (M := M) g α j v y +
        chartPushedRawPartial (I := I) (M := M) g α j w y

  smul : ∀ (c : ℝ) (v : SmoothScalar g),
    chartPushedRawPartial (I := I) (M := M) g α j (c • v) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fun y => c * chartPushedRawPartial (I := I) (M := M) g α j v y

noncomputable def chartPushedRawPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) :=
  (hLip.memLp v).toLp _

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartPushedRawPartialLp_coeFn
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    ((chartPushedRawPartialLp (I := I) (M := M) g α j hLip v :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRawPartial (I := I) (M := M) g α j v := by
  unfold chartPushedRawPartialLp
  exact MeasureTheory.MemLp.coeFn_toLp _

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_chartPushedRawPartialLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    ‖chartPushedRawPartialLp (I := I) (M := M) g α j hLip v‖ =
      ENNReal.toReal (eLpNorm (chartPushedRawPartial (I := I) (M := M) g α j v) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) := by
  unfold chartPushedRawPartialLp
  exact MeasureTheory.Lp.norm_toLp _ _

noncomputable def chartPushedRawPartialLpLin
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j) :
    SmoothScalar g →ₗ[ℝ]
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) where
  toFun v := chartPushedRawPartialLp (I := I) (M := M) g α j hLip v
  map_add' v w := by
    classical
    apply MeasureTheory.Lp.ext
    have h_lhs_coe := chartPushedRawPartialLp_coeFn
      (I := I) (M := M) g α j hLip (v + w)
    have h_v_coe := chartPushedRawPartialLp_coeFn (I := I) (M := M) g α j hLip v
    have h_w_coe := chartPushedRawPartialLp_coeFn (I := I) (M := M) g α j hLip w
    have h_add_aeEq := hLip.add v w
    have h_sum_coe := MeasureTheory.Lp.coeFn_add
      (chartPushedRawPartialLp (I := I) (M := M) g α j hLip v)
      (chartPushedRawPartialLp (I := I) (M := M) g α j hLip w)
    refine h_lhs_coe.trans (h_add_aeEq.trans ?_)
    refine EventuallyEq.symm ?_
    filter_upwards [h_sum_coe, h_v_coe, h_w_coe] with y hy_sum hy_v hy_w
    rw [hy_sum, Pi.add_apply, hy_v, hy_w]
  map_smul' c v := by
    classical
    apply MeasureTheory.Lp.ext
    have h_lhs_coe := chartPushedRawPartialLp_coeFn
      (I := I) (M := M) g α j hLip (c • v)
    have h_v_coe := chartPushedRawPartialLp_coeFn (I := I) (M := M) g α j hLip v
    have h_smul_aeEq := hLip.smul c v
    have h_smul_coe := MeasureTheory.Lp.coeFn_smul c
      (chartPushedRawPartialLp (I := I) (M := M) g α j hLip v)
    refine h_lhs_coe.trans (h_smul_aeEq.trans ?_)
    refine EventuallyEq.symm ?_
    filter_upwards [h_smul_coe, h_v_coe] with y hy_smul hy_v
    change ((c • (chartPushedRawPartialLp (I := I) (M := M) g α j hLip v)) :
        Lp ℝ 2 _) y = c * chartPushedRawPartial (I := I) (M := M) g α j v y
    rw [hy_smul, Pi.smul_apply, hy_v, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] in
lemma chartPushedRawPartialLpLin_apply
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    chartPushedRawPartialLpLin (I := I) (M := M) g α j hLip v =
      chartPushedRawPartialLp (I := I) (M := M) g α j hLip v := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma norm_chartPushedRawPartialLpLin
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    ‖chartPushedRawPartialLpLin (I := I) (M := M) g α j hLip v‖ =
      ENNReal.toReal (eLpNorm (chartPushedRawPartial (I := I) (M := M) g α j v) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) := by
  rw [chartPushedRawPartialLpLin_apply]
  exact norm_chartPushedRawPartialLp (I := I) (M := M) g α j hLip v

noncomputable def chartPushedRawPartialCLM
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j) :
    SmoothScalar g →L[ℝ]
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  (chartPushedRawPartialLpLin (I := I) (M := M) g α j hLip).mkContinuous hLip.C
    (by
      intro v
      rw [norm_chartPushedRawPartialLpLin (I := I) (M := M) g α j hLip v]
      have h_bd := hLip.bound v
      have h_nn := hLip.C_nonneg
      have h_norm_nn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
      have h_lhs_finite : eLpNorm (chartPushedRawPartial (I := I) (M := M) g α j v) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)) ≠ ⊤ :=
        (hLip.memLp v).2.ne
      have h_rhs_eq : ENNReal.ofReal hLip.C * (‖v‖₊ : ℝ≥0∞) =
          ENNReal.ofReal (hLip.C * ‖v‖) := by
        rw [show ((‖v‖₊ : ℝ≥0∞) : ℝ≥0∞) = ENNReal.ofReal ‖v‖ from by
          rw [ENNReal.ofReal, Real.toNNReal_of_nonneg h_norm_nn]
          rfl]
        rw [← ENNReal.ofReal_mul h_nn]
      rw [h_rhs_eq] at h_bd
      have h_toReal := (ENNReal.toReal_le_toReal h_lhs_finite ENNReal.ofReal_ne_top).mpr h_bd
      rwa [ENNReal.toReal_ofReal (mul_nonneg h_nn h_norm_nn)] at h_toReal)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartPushedRawPartialCLM_apply
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    chartPushedRawPartialCLM (I := I) (M := M) g α j hLip v =
      chartPushedRawPartialLp (I := I) (M := M) g α j hLip v := rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma denseRange_smoothToH1Compl_local
    (g : SmoothRiemannianMetric I M) :
    DenseRange (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.denseRange_coe

omit [NeZero (Module.finrank ℝ E)] in
private lemma isUniformInducing_smoothToH1Compl_local
    (g : SmoothRiemannianMetric I M) :
    IsUniformInducing (smoothToH1Compl (I := I) (M := M) g) := by
  unfold smoothToH1Compl
  rw [show (UniformSpace.Completion.toComplL : SmoothScalar g → H1Compl g) =
      ((↑) : SmoothScalar g → UniformSpace.Completion (SmoothScalar g)) from
      UniformSpace.Completion.coe_toComplL]
  exact UniformSpace.Completion.isUniformInducing_coe (SmoothScalar g)

noncomputable def H1ComplRawPartialCLM
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j) :
    H1Compl g →L[ℝ]
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  ContinuousLinearMap.extend
    (chartPushedRawPartialCLM (I := I) (M := M) g α j hLip)
    (smoothToH1Compl (I := I) (M := M) g)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma H1ComplRawPartialCLM_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    H1ComplRawPartialCLM (I := I) (M := M) g α j hLip
        (smoothToH1Compl (I := I) (M := M) g v) =
      chartPushedRawPartialCLM (I := I) (M := M) g α j hLip v := by
  unfold H1ComplRawPartialCLM
  exact ContinuousLinearMap.extend_eq
    (chartPushedRawPartialCLM (I := I) (M := M) g α j hLip)
    (e := smoothToH1Compl (I := I) (M := M) g)
    (denseRange_smoothToH1Compl_local (I := I) (M := M) g)
    (isUniformInducing_smoothToH1Compl_local (I := I) (M := M) g) v

noncomputable def chartPushedRawWeakPartialLp
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (u_h : H1Compl g) :
    Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
      (chartTargetEuclid (I := I) (M := M) α)) :=
  H1ComplRawPartialCLM (I := I) (M := M) g α j hLip u_h

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem chartPushedRawWeakPartialLp_smoothToH1Compl
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    chartPushedRawWeakPartialLp (I := I) (M := M) g α j hLip
        (smoothToH1Compl (I := I) (M := M) g v) =
      chartPushedRawPartialLp (I := I) (M := M) g α j hLip v := by
  unfold chartPushedRawWeakPartialLp
  rw [H1ComplRawPartialCLM_smoothToH1Compl]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedRawWeakPartialLp_continuous
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j) :
    Continuous (chartPushedRawWeakPartialLp (I := I) (M := M) g α j hLip) := by
  unfold chartPushedRawWeakPartialLp
  exact (H1ComplRawPartialCLM (I := I) (M := M) g α j hLip).continuous

omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedRawWeakPartialLp_smoothToH1Compl_coeFn
    (g : SmoothRiemannianMetric I M) (α : M) (j : Fin (Module.finrank ℝ E))
    (hLip : ChartPushedRawPartialLipschitz (I := I) (M := M) g α j)
    (v : SmoothScalar g) :
    ((chartPushedRawWeakPartialLp (I := I) (M := M) g α j hLip
        (smoothToH1Compl (I := I) (M := M) g v) :
        Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRawPartial (I := I) (M := M) g α j v := by
  rw [chartPushedRawWeakPartialLp_smoothToH1Compl]
  exact chartPushedRawPartialLp_coeFn (I := I) (M := M) g α j hLip v

end ChartPushedRawWeakPartialOnVolume
end Laplacian
end Analysis
end DifferentialGeometry

end
