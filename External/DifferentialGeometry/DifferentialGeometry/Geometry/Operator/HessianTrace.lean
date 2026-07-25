import DifferentialGeometry.Geometry.Operator.Hessian
import DifferentialGeometry.Geometry.Operator.VossWeyl
import DifferentialGeometry.Analysis.Integration.Measure.Family
import DifferentialGeometry.Geometry.Operator.HessianTraceChartGramRegularity
import DifferentialGeometry.Geometry.Operator.HessianTraceChartDensityJacobiDerivative
import DifferentialGeometry.Geometry.Operator.HessianTraceChartInverseGramDerivative


noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure

abbrev densityOnE (g : SmoothRiemannianMetric I M) (α : M) : E → ℝ :=
  chartDensityOnE (I := I) g α

def ChartContractedChristoffelOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (y : E) (j : Fin (Module.finrank ℝ E)) : Prop :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α i k y *
        chartChristoffel (I := I) g α i k j y =
    -(1 / chartDensityOnE (I := I) g α y) *
      ∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) l
          (fun y' : E =>
            chartDensityOnE (I := I) g α y' *
              chartInvGramOnE (I := I) g α j l y') y

omit [NeZero (Module.finrank ℝ E)] in
lemma chartHessTrace_expand
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    chartHessTrace (I := I) g f x =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x)) -
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x i j *
                chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) x f) (extChartAt I x x)) := by
  classical
  rw [chartHessTrace_def]
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            chartHessianTensor (I := I) g x f i j x) =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            (chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) x f) (extChartAt I x x))) from ?_]
  swap
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [chartHessianTensor_def]
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            (chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x) -
              ∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) x f) (extChartAt I x x))) =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) g x x i j *
            chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x) -
            chartInvGramMatrix (I := I) g x x i j *
              (∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) x f) (extChartAt I x x)))) from ?_]
  swap
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [show
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartInvGramMatrix (I := I) g x x i j *
            chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x) -
            chartInvGramMatrix (I := I) g x x i j *
              (∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) x f) (extChartAt I x x)))) =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i j *
            chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x)) -
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramMatrix (I := I) g x x i j *
              (∑ k : Fin (Module.finrank ℝ E),
                chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) x f) (extChartAt I x x))) from ?_]
  swap
  · simp only [Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma chartVossWeylLaplacian_expand_hypBearing
    (g : SmoothRiemannianMetric I M) (α : M) (f : M → ℝ) (x : M)
    (hgrad_diff : ∀ i : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (fun y : E => gradChartCoeffOnE (I := I) g α f i y)
        (extChartAt I α x))
    (hdens_diff :
      DifferentiableAt ℝ (chartDensityOnE (I := I) g α) (extChartAt I α x)) :
    chartVossWeylLaplacian (I := I) g α f x =
      (1 / chartDensity (I := I) g α x) *
        ∑ i : Fin (Module.finrank ℝ E),
          (gradChartCoeffOnE (I := I) g α f i (extChartAt I α x) *
            partialDeriv (E := E) i
              (chartDensityOnE (I := I) g α) (extChartAt I α x) +
              chartDensityOnE (I := I) g α (extChartAt I α x) *
                partialDeriv (E := E) i
                  (gradChartCoeffOnE (I := I) g α f i) (extChartAt I α x)) := by
  classical
  rw [chartVossWeylLaplacian_def]
  have hsummand : ∀ i : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i
          (chartVossWeylIntegrand (I := I) g α f i)
          (extChartAt I α x) =
        gradChartCoeffOnE (I := I) g α f i (extChartAt I α x) *
          partialDeriv (E := E) i
            (chartDensityOnE (I := I) g α) (extChartAt I α x) +
          chartDensityOnE (I := I) g α (extChartAt I α x) *
            partialDeriv (E := E) i
              (gradChartCoeffOnE (I := I) g α f i) (extChartAt I α x) := by
    intro i
    have hu : DifferentiableAt ℝ (gradChartCoeffOnE (I := I) g α f i)
        (extChartAt I α x) := hgrad_diff i
    have hv : DifferentiableAt ℝ (chartDensityOnE (I := I) g α)
        (extChartAt I α x) := hdens_diff
    change partialDeriv (E := E) i
        (fun y : E => gradChartCoeffOnE (I := I) g α f i y *
          chartDensityOnE (I := I) g α y) (extChartAt I α x) =
      gradChartCoeffOnE (I := I) g α f i (extChartAt I α x) *
          partialDeriv (E := E) i (chartDensityOnE (I := I) g α) (extChartAt I α x) +
        chartDensityOnE (I := I) g α (extChartAt I α x) *
          partialDeriv (E := E) i
            (gradChartCoeffOnE (I := I) g α f i) (extChartAt I α x)
    unfold partialDeriv
    rw [fderiv_fun_mul (𝕜 := ℝ) hu hv]
    simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) i
              (chartVossWeylIntegrand (I := I) g α f i)
              (extChartAt I α x)) =
        ∑ i : Fin (Module.finrank ℝ E),
          (gradChartCoeffOnE (I := I) g α f i (extChartAt I α x) *
              partialDeriv (E := E) i
                (chartDensityOnE (I := I) g α) (extChartAt I α x) +
            chartDensityOnE (I := I) g α (extChartAt I α x) *
              partialDeriv (E := E) i
                (gradChartCoeffOnE (I := I) g α f i) (extChartAt I α x)) from
      Finset.sum_congr rfl (fun i _ => hsummand i)]
  rw [div_eq_mul_one_div]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem chartHessTrace_eq_laplacian
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j) :
    chartHessTrace (I := I) g f x = Δ_g (I := I) g hf x := by
  classical
  set y₀ : E := extChartAt I x x with hy₀_def
  set α : M := x with hα_def
  have hxsrc : x ∈ (chartAt H α).source := mem_chart_source H x
  have hVW : Δ_g (I := I) g hf x = chartVossWeylLaplacian (I := I) g α f x :=
    voss_weyl_laplacian_formula_of_closed (I := I) g α hf hxsrc
  rw [hVW]
  rw [chartHessTrace_expand (I := I) g f x]
  have hxsrc_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hxsrc
  have hsymm_y₀ : (extChartAt I α).symm y₀ = x :=
    (extChartAt I α).left_inv hxsrc_ext
  have hG_eq : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j =
        chartInvGramOnE (I := I) g α i j y₀ := by
    intros i j
    rw [chartInvGramOnE_def]
    rw [hsymm_y₀]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x i j *
                chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartIteratedPartialDeriv (I := I) α f i j y₀) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hG_eq i j]]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x i j *
                  chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                    partialDeriv (E := E) k
                      (scalarOnE (I := I) x f) (extChartAt I x x)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                chartChristoffel (I := I) g α i j k y₀ *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) α f) y₀) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hG_eq i j]]
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hxsrc
  have hy₀_target : y₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc_ext
  have hy₀_int : y₀ ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hy₀_target
  have hy₀_nhd : interior (extChartAt I α).target ∈ 𝓝 y₀ :=
    isOpen_interior.mem_nhds hy₀_int
  have hgrad_diff : ∀ i : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (gradChartCoeffOnE (I := I) g α f i) y₀ := by
    intro i
    have h := gradChartCoeffOnE_contDiffOn_interior (I := I) g α hf i
    exact (h.contDiffAt hy₀_nhd).differentiableAt (by simp)
  have hdens_diff : DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y₀ := by
    have hcd_target : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g α)
        (extChartAt I α).target := chartDensityOnE_contDiffOn (I := I) g α
    have hcd_int : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g α)
        (interior (extChartAt I α).target) := hcd_target.mono interior_subset
    exact (hcd_int.contDiffAt hy₀_nhd).differentiableAt (by simp)
  have hD_pos : 0 < chartDensity (I := I) g α x :=
    chartDensity_pos (I := I) g α hxbase
  have hD_eq : chartDensityOnE (I := I) g α y₀ = chartDensity (I := I) g α x := by
    unfold chartDensityOnE
    rw [hsymm_y₀]
  rw [chartVossWeylLaplacian_expand_hypBearing (I := I) g α f x
      hgrad_diff hdens_diff]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
              (gradChartCoeffOnE (I := I) g α f i (extChartAt I α x) *
                partialDeriv (E := E) i
                  (chartDensityOnE (I := I) g α) (extChartAt I α x) +
                chartDensityOnE (I := I) g α (extChartAt I α x) *
                  partialDeriv (E := E) i
                    (gradChartCoeffOnE (I := I) g α f i) (extChartAt I α x))) =
        (∑ i : Fin (Module.finrank ℝ E),
          (gradChartCoeffOnE (I := I) g α f i y₀ *
            partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
            chartDensityOnE (I := I) g α y₀ *
              ∑ j : Fin (Module.finrank ℝ E),
                (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀))) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [partialDeriv_gradChartCoeffOnE_expand (I := I) g α hf i hy₀_int]]
  have hT2_swap : (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartChristoffel (I := I) g α i j k y₀ *
                partialDeriv (E := E) k
                  (scalarOnE (I := I) α f) y₀) =
      (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartChristoffel (I := I) g α i j k y₀)) := by
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartChristoffel (I := I) g α i j k y₀ *
                      partialDeriv (E := E) k
                        (scalarOnE (I := I) α f) y₀) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                  (chartInvGramOnE (I := I) g α i j y₀ *
                    chartChristoffel (I := I) g α i j k y₀)) from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                    (chartInvGramOnE (I := I) g α i j y₀ *
                      chartChristoffel (I := I) g α i j k y₀)) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                  (chartInvGramOnE (I := I) g α i j y₀ *
                    chartChristoffel (I := I) g α i j k y₀)) from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  rw [hT2_swap]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartChristoffel (I := I) g α i j k y₀)) =
      (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
          (-(1 / chartDensityOnE (I := I) g α y₀) *
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) l
                (fun y' : E =>
                  chartDensityOnE (I := I) g α y' *
                    chartInvGramOnE (I := I) g α k l y') y₀)) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hcc k]]
  have hDens_diffAt : DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y₀ :=
    hdens_diff
  have hG_diffAt : ∀ k l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartInvGramOnE (I := I) g α k l) y₀ := by
    intro k l
    have hcd_target := chartInvGramOnE_contDiffOn (I := I) g α k l
    have hcd_int := hcd_target.mono interior_subset
    exact (hcd_int.contDiffAt hy₀_nhd).differentiableAt (by simp)
  have hLeibniz : ∀ k l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) l
          (fun y' : E => chartDensityOnE (I := I) g α y' *
            chartInvGramOnE (I := I) g α k l y') y₀ =
        partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
            chartInvGramOnE (I := I) g α k l y₀ +
          chartDensityOnE (I := I) g α y₀ *
            partialDeriv (E := E) l (chartInvGramOnE (I := I) g α k l) y₀ := by
    intro k l
    unfold partialDeriv
    rw [fderiv_fun_mul (𝕜 := ℝ) hDens_diffAt (hG_diffAt k l)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
          (-(1 / chartDensityOnE (I := I) g α y₀) *
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) l
                (fun y' : E =>
                  chartDensityOnE (I := I) g α y' *
                    chartInvGramOnE (I := I) g α k l y') y₀)) =
      (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
          (-(1 / chartDensityOnE (I := I) g α y₀) *
            ∑ l : Fin (Module.finrank ℝ E),
              (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                  chartInvGramOnE (I := I) g α k l y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  partialDeriv (E := E) l
                    (chartInvGramOnE (I := I) g α k l) y₀))) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 2
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hLeibniz k l]]
  have hgrad_eval : ∀ i : Fin (Module.finrank ℝ E),
      gradChartCoeffOnE (I := I) g α f i y₀ =
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i j y₀ *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ := fun i => rfl
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            (gradChartCoeffOnE (I := I) g α f i y₀ *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                ∑ j : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀))) =
        (∑ i : Fin (Module.finrank ℝ E),
          ((∑ j : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀) *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                ∑ j : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀))) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hgrad_eval i]]
  have hG_sym : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α i j y₀ =
        chartInvGramOnE (I := I) g α j i y₀ := by
    intro i j
    unfold chartInvGramOnE chartInvGramMatrix
    set z : M := (extChartAt I α).symm y₀
    have hG_hermit : (chartGramMatrix (I := I) g α z).IsHermitian :=
      chartGramMatrix_isHermitian (I := I) g α z
    have hGinv_hermit : (chartGramMatrix (I := I) g α z)⁻¹.IsHermitian :=
      hG_hermit.inv
    have hentry := hGinv_hermit.apply i j
    have hpoint : (chartGramMatrix (I := I) g α z)⁻¹ i j =
        (chartGramMatrix (I := I) g α z)⁻¹ j i := by
      have hstar : star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
          (chartGramMatrix (I := I) g α z)⁻¹ i j := hentry
      rw [show star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
          (chartGramMatrix (I := I) g α z)⁻¹ j i from rfl] at hstar
      exact hstar.symm
    exact hpoint
  have hDOnE_ne : chartDensityOnE (I := I) g α y₀ ≠ 0 := by
    rw [hD_eq]; exact ne_of_gt hD_pos
  have hDx_ne : chartDensity (I := I) g α x ≠ 0 := ne_of_gt hD_pos
  rw [show
      (1 / chartDensity (I := I) g α x) *
        ∑ i : Fin (Module.finrank ℝ E),
          ((∑ j : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀) *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                ∑ j : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀)) =
        (1 / chartDensity (I := I) g α x) *
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartInvGramOnE (I := I) g α i j y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                  partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  (partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀)) from by
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]]
  rw [show (1 / chartDensity (I := I) g α x) *
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (chartInvGramOnE (I := I) g α i j y₀ *
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                (partialDeriv (E := E) i
                    (chartInvGramOnE (I := I) g α i j) y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((1 / chartDensity (I := I) g α x) *
            (chartInvGramOnE (I := I) g α i j y₀ *
              partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀) +
            (1 / chartDensity (I := I) g α x) *
              (chartDensityOnE (I := I) g α y₀ *
                (partialDeriv (E := E) i
                    (chartInvGramOnE (I := I) g α i j) y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀))) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) k
                (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀) *
                ∑ l : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                      chartInvGramOnE (I := I) g α k l y₀ +
                    chartDensityOnE (I := I) g α y₀ *
                      partialDeriv (E := E) l
                        (chartInvGramOnE (I := I) g α k l) y₀))) =
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀)) *
              (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                chartInvGramOnE (I := I) g α k l y₀ +
              chartDensityOnE (I := I) g α y₀ *
                partialDeriv (E := E) l
                  (chartInvGramOnE (I := I) g α k l) y₀)) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                (-(1 / chartDensityOnE (I := I) g α y₀)) *
                (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                  chartInvGramOnE (I := I) g α k l y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  partialDeriv (E := E) l
                    (chartInvGramOnE (I := I) g α k l) y₀)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀)) *
              (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                chartInvGramOnE (I := I) g α j i y₀ +
              chartDensityOnE (I := I) g α y₀ *
                partialDeriv (E := E) i
                  (chartInvGramOnE (I := I) g α j i) y₀)) from by
    rw [Finset.sum_comm]]
  have h_partial_swap : ∀ i j : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j i) y₀ =
        partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ := by
    intros i j
    have hfun_eq : chartInvGramOnE (I := I) g α j i =
        chartInvGramOnE (I := I) g α i j := by
      funext y'
      unfold chartInvGramOnE
      set z' : M := (extChartAt I α).symm y'
      have hz_hermit : (chartGramMatrix (I := I) g α z').IsHermitian :=
        chartGramMatrix_isHermitian (I := I) g α z'
      have hzinv_hermit : (chartGramMatrix (I := I) g α z')⁻¹.IsHermitian :=
        hz_hermit.inv
      have hentry := hzinv_hermit.apply i j
      have hstar_eq : (chartGramMatrix (I := I) g α z')⁻¹ j i =
          (chartGramMatrix (I := I) g α z')⁻¹ i j := by
        have hstar : star ((chartGramMatrix (I := I) g α z')⁻¹ j i) =
            (chartGramMatrix (I := I) g α z')⁻¹ i j := hentry
        rw [show star ((chartGramMatrix (I := I) g α z')⁻¹ j i) =
            (chartGramMatrix (I := I) g α z')⁻¹ j i from rfl] at hstar
        exact hstar
      change (chartGramMatrix (I := I) g α z')⁻¹ j i =
          (chartGramMatrix (I := I) g α z')⁻¹ i j
      exact hstar_eq
    rw [hfun_eq]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                (-(1 / chartDensityOnE (I := I) g α y₀)) *
                (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                  chartInvGramOnE (I := I) g α j i y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  partialDeriv (E := E) i
                    (chartInvGramOnE (I := I) g α j i) y₀)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀)) *
              (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                chartInvGramOnE (I := I) g α i j y₀ +
              chartDensityOnE (I := I) g α y₀ *
                partialDeriv (E := E) i
                  (chartInvGramOnE (I := I) g α i j) y₀)) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hG_sym j i]
    rw [h_partial_swap i j]]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                chartIteratedPartialDeriv (I := I) α f i j y₀) -
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                  (-(1 / chartDensityOnE (I := I) g α y₀)) *
                  (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                    chartInvGramOnE (I := I) g α i j y₀ +
                  chartDensityOnE (I := I) g α y₀ *
                    partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α i j) y₀)) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀ -
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                  (-(1 / chartDensityOnE (I := I) g α y₀)) *
                  (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                    chartInvGramOnE (I := I) g α i j y₀ +
                  chartDensityOnE (I := I) g α y₀ *
                    partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α i j) y₀))) from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hD_eq]
  field_simp
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem traceFun_hessFun_eq_chartHessTrace_of_orthonormal
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      chartHessTrace (I := I) g f x := by
  classical
  rw [traceFun_hessFun, chartHessTrace_def]
  symm
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · rw [h_orth i i, if_pos rfl, one_mul]
  · intro j _ hji
    have hij : ¬ i = j := fun h => hji h.symm
    rw [h_orth i j, if_neg hij, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

omit [NeZero (Module.finrank ℝ E)] in
theorem trace_hessFun_eq_laplacian
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j) :
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x i j *
          chartHessianTensor (I := I) g x f i j x =
      Δ_g (I := I) g hf x := by
  have h := chartHessTrace_eq_laplacian (I := I) g hf x hcc
  rw [chartHessTrace_def] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacian_sq_le_dim_mul_frobenius_sq_via_chartContracted
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    (Δ_g (I := I) g hf x)^2 ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartHessianTensor (I := I) g x f i j x)^2 := by
  classical
  have h1 : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      chartHessTrace (I := I) g f x :=
    traceFun_hessFun_eq_chartHessTrace_of_orthonormal (I := I) g f x h_orth
  have h2 : chartHessTrace (I := I) g f x = Δ_g (I := I) g hf x :=
    chartHessTrace_eq_laplacian (I := I) g hf x hcc
  have htr : traceFun (I := I) (M := M) (hessFun (I := I) g f) x =
      Δ_g (I := I) g hf x := h1.trans h2
  exact laplacian_sq_le_dim_mul_frobenius_sq_of_trace_eq
    (I := I) g hf x htr

omit [NeZero (Module.finrank ℝ E)] in
theorem chartContractedChristoffel_holds
    (g : SmoothRiemannianMetric I M) (α : M)
    (y : E) (j : Fin (Module.finrank ℝ E))
    (hy : y ∈ interior (extChartAt I α).target) :
    ChartContractedChristoffelOn (I := I) g α y j := by
  classical
  unfold ChartContractedChristoffelOn
  set y₀ := y with hy₀_def
  have hytgt : y₀ ∈ (extChartAt I α).target := interior_subset hy
  have hz_base : (extChartAt I α).symm y₀ ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    have hsource : (extChartAt I α).symm y₀ ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hytgt
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hD_pos : 0 < chartDensityOnE (I := I) g α y₀ := by
    unfold chartDensityOnE
    exact chartDensity_pos (I := I) g α hz_base
  have hD_ne : chartDensityOnE (I := I) g α y₀ ≠ 0 := ne_of_gt hD_pos
  set D : ℝ := chartDensityOnE (I := I) g α y₀ with hD_def
  set GU : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i k => chartInvGramOnE (I := I) g α i k y₀ with hGU_def
  set GD : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i k => chartGramOnE (I := I) g α i k y₀ with hGD_def
  set dGD : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun l a b => partialDeriv (E := E) l (chartGramOnE (I := I) g α a b) y₀ with hdGD_def
  set dGU : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ :=
    fun l a b => partialDeriv (E := E) l (chartInvGramOnE (I := I) g α a b) y₀ with hdGU_def
  set dD : Fin (Module.finrank ℝ E) → ℝ :=
    fun l => partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ with hdD_def
  have hLHS_expand : ∑ i : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α i k y₀ *
          chartChristoffel (I := I) g α i k j y₀ =
        (1 / 2 : ℝ) *
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                GU i k * GU j l *
                  (dGD i l k + dGD k l i - dGD l i k) := by
    have hstep1 : ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i k y₀ *
            chartChristoffel (I := I) g α i k j y₀ =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i k y₀ *
              ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y₀) j l *
                  (partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y₀ +
                   partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y₀ -
                   partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y₀)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [chartChristoffel_def]
    rw [hstep1]
    rw [show (1 / 2 : ℝ) *
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  GU i k * GU j l * (dGD i l k + dGD k l i - dGD l i k) =
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              (1 / 2 : ℝ) *
                (GU i k * GU j l * (dGD i l k + dGD k l i - dGD l i k)) from by
      simp only [Finset.mul_sum]]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show chartInvGramOnE (I := I) g α i k y₀ *
            ((1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y₀) j l *
                (partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y₀ +
                  partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y₀ -
                  partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y₀)) =
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i k y₀ *
            ((1 / 2 : ℝ) *
              (chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y₀) j l *
                (partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y₀ +
                  partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y₀ -
                  partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y₀))) from by
      simp only [Finset.mul_sum]]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hGUjl : GU j l =
        chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y₀) j l := rfl
    have hGUik : GU i k = chartInvGramOnE (I := I) g α i k y₀ := rfl
    rw [hGUjl, hGUik]
    ring
  have hsym_swap : ∀ l : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          GU i k * GU j l * dGD i l k) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            GU i k * GU j l * dGD k l i) := by
    intro l
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                GU i k * GU j l * dGD i l k) =
          (∑ k : Fin (Module.finrank ℝ E),
            ∑ i : Fin (Module.finrank ℝ E),
              GU i k * GU j l * dGD i l k) from Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    change GU k i * GU j l * dGD k l i = GU i k * GU j l * dGD k l i
    have hGUki : GU k i = GU i k := by
      change chartInvGramOnE (I := I) g α k i y₀ = chartInvGramOnE (I := I) g α i k y₀
      exact chartInvGramOnE_symm_pointwise (I := I) g α k i y₀
    rw [hGUki]
  have hLHS_simplified : ∑ i : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) g α i k y₀ *
          chartChristoffel (I := I) g α i k j y₀ =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              GU i k * GU j l * dGD i l k) -
        (1 / 2 : ℝ) *
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                GU i k * GU j l * dGD l i k) := by
    rw [hLHS_expand]
    rw [show
      ∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              GU i k * GU j l * (dGD i l k + dGD k l i - dGD l i k) =
      ∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              (GU i k * GU j l * dGD i l k + GU i k * GU j l * dGD k l i -
                GU i k * GU j l * dGD l i k) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hsecond_eq : ∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            GU i k * GU j l * dGD k l i =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                GU i k * GU j l * dGD i l k := by
      rw [show ∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  GU i k * GU j l * dGD k l i =
            ∑ l : Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  GU i k * GU j l * dGD k l i from by
        rw [show (∑ i : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  ∑ l : Fin (Module.finrank ℝ E),
                    GU i k * GU j l * dGD k l i) =
              (∑ i : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ∑ k : Fin (Module.finrank ℝ E),
                    GU i k * GU j l * dGD k l i) from by
          refine Finset.sum_congr rfl (fun _ _ => ?_)
          rw [Finset.sum_comm]]
        rw [Finset.sum_comm]]
      rw [show ∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  GU i k * GU j l * dGD i l k =
            ∑ l : Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  GU i k * GU j l * dGD i l k from by
        rw [show (∑ i : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  ∑ l : Fin (Module.finrank ℝ E),
                    GU i k * GU j l * dGD i l k) =
              (∑ i : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  ∑ k : Fin (Module.finrank ℝ E),
                    GU i k * GU j l * dGD i l k) from by
          refine Finset.sum_congr rfl (fun _ _ => ?_)
          rw [Finset.sum_comm]]
        rw [Finset.sum_comm]]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      exact (hsym_swap l).symm
    rw [hsecond_eq]
    ring
  have hT_eq : ∑ i : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          GU i k * GU j l * dGD i l k =
        -(∑ a : Fin (Module.finrank ℝ E), dGU a j a) := by
    have hidentity : ∀ a : Fin (Module.finrank ℝ E),
        dGU a j a =
          -∑ p : Fin (Module.finrank ℝ E),
            ∑ q : Fin (Module.finrank ℝ E),
              GU j p * GU q a * dGD a p q := by
      intro a
      change partialDeriv (E := E) a (chartInvGramOnE (I := I) g α j a) y₀ =
          -∑ p : Fin (Module.finrank ℝ E),
            ∑ q : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α j p y₀ *
                chartInvGramOnE (I := I) g α q a y₀ *
                partialDeriv (E := E) a (chartGramOnE (I := I) g α p q) y₀
      rw [partialDeriv_chartInvGramOnE_eq (I := I) g α y₀ a j a hy]
    have hsum_dGU : ∑ a : Fin (Module.finrank ℝ E), dGU a j a =
        -∑ a : Fin (Module.finrank ℝ E),
          ∑ p : Fin (Module.finrank ℝ E),
            ∑ q : Fin (Module.finrank ℝ E),
              GU j p * GU q a * dGD a p q := by
      rw [show (∑ a : Fin (Module.finrank ℝ E), dGU a j a) =
          ∑ a : Fin (Module.finrank ℝ E),
            -∑ p : Fin (Module.finrank ℝ E),
              ∑ q : Fin (Module.finrank ℝ E),
                GU j p * GU q a * dGD a p q from
            Finset.sum_congr rfl (fun a _ => hidentity a)]
      rw [Finset.sum_neg_distrib]
    rw [hsum_dGU]
    rw [neg_neg]
    rw [show (∑ a : Fin (Module.finrank ℝ E),
              ∑ p : Fin (Module.finrank ℝ E),
                ∑ q : Fin (Module.finrank ℝ E),
                  GU j p * GU q a * dGD a p q) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                GU j l * GU k i * dGD i l k) from rfl]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  GU j l * GU k i * dGD i l k) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                GU j l * GU i k * dGD i l k) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun l _ => ?_)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hGUki : GU k i = GU i k := by
        change chartInvGramOnE (I := I) g α k i y₀ = chartInvGramOnE (I := I) g α i k y₀
        exact chartInvGramOnE_symm_pointwise (I := I) g α k i y₀
      rw [hGUki]]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  GU j l * GU i k * dGD i l k) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                GU j l * GU i k * dGD i l k) from by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_comm]]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  have hSecondTriple : (1 / 2 : ℝ) *
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            GU i k * GU j l * dGD l i k) =
        ∑ l : Fin (Module.finrank ℝ E),
          GU j l * (dD l / D) := by
    have hfor_each_l : ∀ l : Fin (Module.finrank ℝ E),
        (1 / 2 : ℝ) * (∑ i : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E), GU i k * dGD l i k) = dD l / D := by
      intro l
      have hjac := partialDeriv_chartDensityOnE (I := I) g α y₀ l hy
      have htrace_expand :
          Matrix.trace ((chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀))⁻¹ *
            Matrix.of (fun i j => partialDeriv (E := E) l
              (chartGramOnE (I := I) g α i j) y₀)) =
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                GU i k * dGD l i k := by
        simp only [Matrix.trace, Matrix.mul_apply, Matrix.diag, Matrix.of_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        have hGUik : GU i k = (chartGramMatrix (I := I) g α ((extChartAt I α).symm y₀))⁻¹ i k := rfl
        have hdGDlik : dGD l i k = partialDeriv (E := E) l (chartGramOnE (I := I) g α i k) y₀ := rfl
        rw [hGUik, hdGDlik, ← chartGramOnE_symm_fun (I := I) g α k i]
      rw [htrace_expand] at hjac
      have hfact : dD l = (1 / 2 : ℝ) *
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              GU i k * dGD l i k) * D := by
        rw [hdD_def, hD_def]
        exact hjac
      rw [hfact]
      field_simp
    rw [show (1 / 2 : ℝ) *
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  GU i k * GU j l * dGD l i k) =
        (1 / 2 : ℝ) *
            ∑ l : Fin (Module.finrank ℝ E),
              GU j l * (∑ i : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E), GU i k * dGD l i k) from by
      congr 1
      rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  GU i k * GU j l * dGD l i k) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                GU i k * GU j l * dGD l i k) from by
        refine Finset.sum_congr rfl (fun _ _ => ?_)
        rw [Finset.sum_comm]]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (1 / 2 : ℝ) *
            (GU j l * (∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E), GU i k * dGD l i k)) =
        GU j l * ((1 / 2 : ℝ) *
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E), GU i k * dGD l i k)) from by ring]
    rw [hfor_each_l l]
  rw [hLHS_simplified]
  rw [hT_eq, hSecondTriple]
  have hRHS_expand : -(1 / D) *
      ∑ l : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) l
          (fun y' : E =>
            chartDensityOnE (I := I) g α y' *
              chartInvGramOnE (I := I) g α j l y') y₀ =
      -∑ l : Fin (Module.finrank ℝ E),
        (GU j l * (dD l / D) + dGU l j l) := by
    rw [show -(1 / D) *
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) l
                (fun y' : E =>
                  chartDensityOnE (I := I) g α y' *
                    chartInvGramOnE (I := I) g α j l y') y₀ =
        -((1 / D) *
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) l
                (fun y' : E =>
                  chartDensityOnE (I := I) g α y' *
                    chartInvGramOnE (I := I) g α j l y') y₀) from by ring]
    congr 1
    rw [show (1 / D) *
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) l
                (fun y' : E =>
                  chartDensityOnE (I := I) g α y' *
                    chartInvGramOnE (I := I) g α j l y') y₀ =
        ∑ l : Fin (Module.finrank ℝ E),
          (1 / D) * partialDeriv (E := E) l
            (fun y' : E =>
              chartDensityOnE (I := I) g α y' *
                chartInvGramOnE (I := I) g α j l y') y₀ from by
      rw [Finset.mul_sum]]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hdens_diff : DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y₀ :=
      chartDensityOnE_differentiableAt_interior (I := I) g α hy
    have hG_diff : DifferentiableAt ℝ (chartInvGramOnE (I := I) g α j l) y₀ :=
      chartInvGramOnE_differentiableAt_interior (I := I) g α j l hy
    have hLeibniz : partialDeriv (E := E) l
        (fun y' : E => chartDensityOnE (I := I) g α y' *
          chartInvGramOnE (I := I) g α j l y') y₀ =
        partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
            chartInvGramOnE (I := I) g α j l y₀ +
          chartDensityOnE (I := I) g α y₀ *
            partialDeriv (E := E) l (chartInvGramOnE (I := I) g α j l) y₀ := by
      unfold partialDeriv
      rw [fderiv_fun_mul (𝕜 := ℝ) hdens_diff hG_diff]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hLeibniz]
    change (1 / chartDensityOnE (I := I) g α y₀) *
        (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
            chartInvGramOnE (I := I) g α j l y₀ +
          chartDensityOnE (I := I) g α y₀ *
            partialDeriv (E := E) l (chartInvGramOnE (I := I) g α j l) y₀) =
      GU j l * (dD l / D) + dGU l j l
    rw [hdD_def, hGU_def, hdGU_def, hD_def]
    have hDne : chartDensityOnE (I := I) g α y₀ ≠ 0 := hD_ne
    field_simp
  rw [hRHS_expand]
  rw [show -∑ l : Fin (Module.finrank ℝ E),
            (GU j l * (dD l / D) + dGU l j l) =
        -(∑ l : Fin (Module.finrank ℝ E),
          GU j l * (dD l / D)) -
        (∑ l : Fin (Module.finrank ℝ E), dGU l j l) from by
    rw [show ∑ l : Fin (Module.finrank ℝ E),
            (GU j l * (dD l / D) + dGU l j l) =
          (∑ l : Fin (Module.finrank ℝ E), GU j l * (dD l / D)) +
            ∑ l : Fin (Module.finrank ℝ E), dGU l j l from
        Finset.sum_add_distrib]
    ring]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem chartContractedChristoffel_holds_of_boundaryless [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ (extChartAt I α).target)
    (j : Fin (Module.finrank ℝ E)) :
    ChartContractedChristoffelOn (I := I) g α y j := by
  have hy_int : y ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hy
  exact chartContractedChristoffel_holds (I := I) g α y j hy_int

omit [NeZero (Module.finrank ℝ E)] in
theorem chartHessTrace_eq_laplacian_of_boundaryless
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    chartHessTrace (I := I) g f x = Δ_g (I := I) g hf x := by
  classical
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hx_target : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc
  have hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j :=
    fun j => chartContractedChristoffel_holds_of_boundaryless
      (I := I) g x hx_target j
  exact chartHessTrace_eq_laplacian (I := I) g hf x hcc

omit [NeZero (Module.finrank ℝ E)] in
theorem chartInvGram_trace_hessianTensor_eq_laplacian_of_boundaryless
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g x x i j *
          chartHessianTensor (I := I) g x f i j x =
      Δ_g (I := I) g hf x := by
  classical
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hx_target : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc
  have hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j :=
    fun j => chartContractedChristoffel_holds_of_boundaryless
      (I := I) g x hx_target j
  exact trace_hessFun_eq_laplacian (I := I) g hf x hcc

omit [NeZero (Module.finrank ℝ E)] in
theorem laplacian_sq_le_dim_mul_frobenius_sq_of_orthonormal
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    (Δ_g (I := I) g hf x)^2 ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartHessianTensor (I := I) g x f i j x)^2 := by
  classical
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hx_target : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc
  have hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j :=
    fun j => chartContractedChristoffel_holds_of_boundaryless
      (I := I) g x hx_target j
  exact laplacian_sq_le_dim_mul_frobenius_sq_via_chartContracted
    (I := I) g hf x hcc h_orth

omit [NeZero (Module.finrank ℝ E)] in
theorem chartHessTrace_eq_laplacian_pointwise
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j) :
    chartHessTrace (I := I) g f x = Δ_g (I := I) g hf x := by
  classical
  set y₀ : E := extChartAt I x x with hy₀_def
  set α : M := x with hα_def
  have hxsrc : x ∈ (chartAt H α).source := mem_chart_source H x
  have hVW : Δ_g (I := I) g hf x = chartVossWeylLaplacian (I := I) g α f x :=
    voss_weyl_laplacian_formula_pointwise (I := I) g α hf hxsrc
  rw [hVW]
  rw [chartHessTrace_expand (I := I) g f x]
  have hxsrc_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hxsrc
  have hsymm_y₀ : (extChartAt I α).symm y₀ = x :=
    (extChartAt I α).left_inv hxsrc_ext
  have hG_eq : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j =
        chartInvGramOnE (I := I) g α i j y₀ := by
    intros i j
    rw [chartInvGramOnE_def]
    rw [hsymm_y₀]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramMatrix (I := I) g x x i j *
                chartIteratedPartialDeriv (I := I) x f i j (extChartAt I x x)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartIteratedPartialDeriv (I := I) α f i j y₀) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hG_eq i j]]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                chartInvGramMatrix (I := I) g x x i j *
                  chartChristoffel (I := I) g x i j k (extChartAt I x x) *
                    partialDeriv (E := E) k
                      (scalarOnE (I := I) x f) (extChartAt I x x)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                chartChristoffel (I := I) g α i j k y₀ *
                  partialDeriv (E := E) k
                    (scalarOnE (I := I) α f) y₀) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hG_eq i j]]
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hxsrc
  have hy₀_target : y₀ ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hxsrc_ext
  have hy₀_int : y₀ ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α hy₀_target
  have hy₀_nhd : interior (extChartAt I α).target ∈ 𝓝 y₀ :=
    isOpen_interior.mem_nhds hy₀_int
  have hgrad_diff : ∀ i : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (gradChartCoeffOnE (I := I) g α f i) y₀ := by
    intro i
    have h := gradChartCoeffOnE_contDiffOn_interior (I := I) g α hf i
    exact (h.contDiffAt hy₀_nhd).differentiableAt (by simp)
  have hdens_diff : DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y₀ := by
    have hcd_target : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g α)
        (extChartAt I α).target := chartDensityOnE_contDiffOn (I := I) g α
    have hcd_int : ContDiffOn ℝ ∞ (chartDensityOnE (I := I) g α)
        (interior (extChartAt I α).target) := hcd_target.mono interior_subset
    exact (hcd_int.contDiffAt hy₀_nhd).differentiableAt (by simp)
  have hD_pos : 0 < chartDensity (I := I) g α x :=
    chartDensity_pos (I := I) g α hxbase
  have hD_eq : chartDensityOnE (I := I) g α y₀ = chartDensity (I := I) g α x := by
    unfold chartDensityOnE
    rw [hsymm_y₀]
  rw [chartVossWeylLaplacian_expand_hypBearing (I := I) g α f x
      hgrad_diff hdens_diff]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
              (gradChartCoeffOnE (I := I) g α f i (extChartAt I α x) *
                partialDeriv (E := E) i
                  (chartDensityOnE (I := I) g α) (extChartAt I α x) +
                chartDensityOnE (I := I) g α (extChartAt I α x) *
                  partialDeriv (E := E) i
                    (gradChartCoeffOnE (I := I) g α f i) (extChartAt I α x))) =
        (∑ i : Fin (Module.finrank ℝ E),
          (gradChartCoeffOnE (I := I) g α f i y₀ *
            partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
            chartDensityOnE (I := I) g α y₀ *
              ∑ j : Fin (Module.finrank ℝ E),
                (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀))) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [partialDeriv_gradChartCoeffOnE_expand (I := I) g α hf i hy₀_int]]
  have hT2_swap : (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartChristoffel (I := I) g α i j k y₀ *
                partialDeriv (E := E) k
                  (scalarOnE (I := I) α f) y₀) =
      (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartChristoffel (I := I) g α i j k y₀)) := by
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartChristoffel (I := I) g α i j k y₀ *
                      partialDeriv (E := E) k
                        (scalarOnE (I := I) α f) y₀) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ k : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                  (chartInvGramOnE (I := I) g α i j y₀ *
                    chartChristoffel (I := I) g α i j k y₀)) from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring]
    rw [show (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                ∑ k : Fin (Module.finrank ℝ E),
                  partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                    (chartInvGramOnE (I := I) g α i j y₀ *
                      chartChristoffel (I := I) g α i j k y₀)) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                  (chartInvGramOnE (I := I) g α i j y₀ *
                    chartChristoffel (I := I) g α i j k y₀)) from by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  rw [hT2_swap]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramOnE (I := I) g α i j y₀ *
              chartChristoffel (I := I) g α i j k y₀)) =
      (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
          (-(1 / chartDensityOnE (I := I) g α y₀) *
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) l
                (fun y' : E =>
                  chartDensityOnE (I := I) g α y' *
                    chartInvGramOnE (I := I) g α k l y') y₀)) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hcc k]]
  have hDens_diffAt : DifferentiableAt ℝ (chartDensityOnE (I := I) g α) y₀ :=
    hdens_diff
  have hG_diffAt : ∀ k l : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ (chartInvGramOnE (I := I) g α k l) y₀ := by
    intro k l
    have hcd_target := chartInvGramOnE_contDiffOn (I := I) g α k l
    have hcd_int := hcd_target.mono interior_subset
    exact (hcd_int.contDiffAt hy₀_nhd).differentiableAt (by simp)
  have hLeibniz : ∀ k l : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) l
          (fun y' : E => chartDensityOnE (I := I) g α y' *
            chartInvGramOnE (I := I) g α k l y') y₀ =
        partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
            chartInvGramOnE (I := I) g α k l y₀ +
          chartDensityOnE (I := I) g α y₀ *
            partialDeriv (E := E) l (chartInvGramOnE (I := I) g α k l) y₀ := by
    intro k l
    unfold partialDeriv
    rw [fderiv_fun_mul (𝕜 := ℝ) hDens_diffAt (hG_diffAt k l)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  rw [show (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
          (-(1 / chartDensityOnE (I := I) g α y₀) *
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) l
                (fun y' : E =>
                  chartDensityOnE (I := I) g α y' *
                    chartInvGramOnE (I := I) g α k l y') y₀)) =
      (∑ k : Fin (Module.finrank ℝ E),
        partialDeriv (E := E) k
            (scalarOnE (I := I) α f) y₀ *
          (-(1 / chartDensityOnE (I := I) g α y₀) *
            ∑ l : Fin (Module.finrank ℝ E),
              (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                  chartInvGramOnE (I := I) g α k l y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  partialDeriv (E := E) l
                    (chartInvGramOnE (I := I) g α k l) y₀))) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 2
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hLeibniz k l]]
  have hgrad_eval : ∀ i : Fin (Module.finrank ℝ E),
      gradChartCoeffOnE (I := I) g α f i y₀ =
        ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α i j y₀ *
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ := fun i => rfl
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            (gradChartCoeffOnE (I := I) g α f i y₀ *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                ∑ j : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀))) =
        (∑ i : Fin (Module.finrank ℝ E),
          ((∑ j : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀) *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                ∑ j : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀))) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hgrad_eval i]]
  have hG_sym : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g α i j y₀ =
        chartInvGramOnE (I := I) g α j i y₀ := by
    intro i j
    unfold chartInvGramOnE chartInvGramMatrix
    set z : M := (extChartAt I α).symm y₀
    have hG_hermit : (chartGramMatrix (I := I) g α z).IsHermitian :=
      chartGramMatrix_isHermitian (I := I) g α z
    have hGinv_hermit : (chartGramMatrix (I := I) g α z)⁻¹.IsHermitian :=
      hG_hermit.inv
    have hentry := hGinv_hermit.apply i j
    have hpoint : (chartGramMatrix (I := I) g α z)⁻¹ i j =
        (chartGramMatrix (I := I) g α z)⁻¹ j i := by
      have hstar : star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
          (chartGramMatrix (I := I) g α z)⁻¹ i j := hentry
      rw [show star ((chartGramMatrix (I := I) g α z)⁻¹ j i) =
          (chartGramMatrix (I := I) g α z)⁻¹ j i from rfl] at hstar
      exact hstar.symm
    exact hpoint
  have hDOnE_ne : chartDensityOnE (I := I) g α y₀ ≠ 0 := by
    rw [hD_eq]; exact ne_of_gt hD_pos
  have hDx_ne : chartDensity (I := I) g α x ≠ 0 := ne_of_gt hD_pos
  rw [show
      (1 / chartDensity (I := I) g α x) *
        ∑ i : Fin (Module.finrank ℝ E),
          ((∑ j : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀) *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                ∑ j : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀)) =
        (1 / chartDensity (I := I) g α x) *
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartInvGramOnE (I := I) g α i j y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                  partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  (partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α i j) y₀ *
                    partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                  chartInvGramOnE (I := I) g α i j y₀ *
                    chartIteratedPartialDeriv (I := I) α f i j y₀)) from by
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]]
  rw [show (1 / chartDensity (I := I) g α x) *
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (chartInvGramOnE (I := I) g α i j y₀ *
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ +
              chartDensityOnE (I := I) g α y₀ *
                (partialDeriv (E := E) i
                    (chartInvGramOnE (I := I) g α i j) y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀)) =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ((1 / chartDensity (I := I) g α x) *
            (chartInvGramOnE (I := I) g α i j y₀ *
              partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
              partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀) +
            (1 / chartDensity (I := I) g α x) *
              (chartDensityOnE (I := I) g α y₀ *
                (partialDeriv (E := E) i
                    (chartInvGramOnE (I := I) g α i j) y₀ *
                  partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ +
                chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀))) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) k
                (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀) *
                ∑ l : Fin (Module.finrank ℝ E),
                  (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                      chartInvGramOnE (I := I) g α k l y₀ +
                    chartDensityOnE (I := I) g α y₀ *
                      partialDeriv (E := E) l
                        (chartInvGramOnE (I := I) g α k l) y₀))) =
        (∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀)) *
              (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                chartInvGramOnE (I := I) g α k l y₀ +
              chartDensityOnE (I := I) g α y₀ *
                partialDeriv (E := E) l
                  (chartInvGramOnE (I := I) g α k l) y₀)) from by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring]
  rw [show (∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) k (scalarOnE (I := I) α f) y₀ *
                (-(1 / chartDensityOnE (I := I) g α y₀)) *
                (partialDeriv (E := E) l (chartDensityOnE (I := I) g α) y₀ *
                  chartInvGramOnE (I := I) g α k l y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  partialDeriv (E := E) l
                    (chartInvGramOnE (I := I) g α k l) y₀)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀)) *
              (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                chartInvGramOnE (I := I) g α j i y₀ +
              chartDensityOnE (I := I) g α y₀ *
                partialDeriv (E := E) i
                  (chartInvGramOnE (I := I) g α j i) y₀)) from by
    rw [Finset.sum_comm]]
  have h_partial_swap : ∀ i j : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) i (chartInvGramOnE (I := I) g α j i) y₀ =
        partialDeriv (E := E) i (chartInvGramOnE (I := I) g α i j) y₀ := by
    intros i j
    have hfun_eq : chartInvGramOnE (I := I) g α j i =
        chartInvGramOnE (I := I) g α i j := by
      funext y'
      unfold chartInvGramOnE
      set z' : M := (extChartAt I α).symm y'
      have hz_hermit : (chartGramMatrix (I := I) g α z').IsHermitian :=
        chartGramMatrix_isHermitian (I := I) g α z'
      have hzinv_hermit : (chartGramMatrix (I := I) g α z')⁻¹.IsHermitian :=
        hz_hermit.inv
      have hentry := hzinv_hermit.apply i j
      have hstar_eq : (chartGramMatrix (I := I) g α z')⁻¹ j i =
          (chartGramMatrix (I := I) g α z')⁻¹ i j := by
        have hstar : star ((chartGramMatrix (I := I) g α z')⁻¹ j i) =
            (chartGramMatrix (I := I) g α z')⁻¹ i j := hentry
        rw [show star ((chartGramMatrix (I := I) g α z')⁻¹ j i) =
            (chartGramMatrix (I := I) g α z')⁻¹ j i from rfl] at hstar
        exact hstar
      change (chartGramMatrix (I := I) g α z')⁻¹ j i =
          (chartGramMatrix (I := I) g α z')⁻¹ i j
      exact hstar_eq
    rw [hfun_eq]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                (-(1 / chartDensityOnE (I := I) g α y₀)) *
                (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                  chartInvGramOnE (I := I) g α j i y₀ +
                chartDensityOnE (I := I) g α y₀ *
                  partialDeriv (E := E) i
                    (chartInvGramOnE (I := I) g α j i) y₀)) =
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
              (-(1 / chartDensityOnE (I := I) g α y₀)) *
              (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                chartInvGramOnE (I := I) g α i j y₀ +
              chartDensityOnE (I := I) g α y₀ *
                partialDeriv (E := E) i
                  (chartInvGramOnE (I := I) g α i j) y₀)) from by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hG_sym j i]
    rw [h_partial_swap i j]]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramOnE (I := I) g α i j y₀ *
                chartIteratedPartialDeriv (I := I) α f i j y₀) -
            (∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                  (-(1 / chartDensityOnE (I := I) g α y₀)) *
                  (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                    chartInvGramOnE (I := I) g α i j y₀ +
                  chartDensityOnE (I := I) g α y₀ *
                    partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α i j) y₀)) =
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartInvGramOnE (I := I) g α i j y₀ *
                  chartIteratedPartialDeriv (I := I) α f i j y₀ -
                partialDeriv (E := E) j (scalarOnE (I := I) α f) y₀ *
                  (-(1 / chartDensityOnE (I := I) g α y₀)) *
                  (partialDeriv (E := E) i (chartDensityOnE (I := I) g α) y₀ *
                    chartInvGramOnE (I := I) g α i j y₀ +
                  chartDensityOnE (I := I) g α y₀ *
                    partialDeriv (E := E) i
                      (chartInvGramOnE (I := I) g α i j) y₀))) from by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib]]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hD_eq]
  field_simp
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem chartHessTrace_eq_laplacian_pointwise_of_boundaryless
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    chartHessTrace (I := I) g f x = Δ_g (I := I) g hf x := by
  classical
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact mem_chart_source H x
  have hx_target : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hxsrc
  have hcc : ∀ j : Fin (Module.finrank ℝ E),
      ChartContractedChristoffelOn (I := I) g x (extChartAt I x x) j :=
    fun j => chartContractedChristoffel_holds_of_boundaryless
      (I := I) g x hx_target j
  exact chartHessTrace_eq_laplacian_pointwise (I := I) g hf x hcc

end DivergenceTheorem
end Integral
end DifferentialGeometry
