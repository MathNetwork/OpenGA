import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplResidualMemW1p
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplResidualChain
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.Laplacian.LpIdentity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1ComplResidual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualMemW1p
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def diffChartBilinearH1ComplData_of_smoothToH1Compl_unconditional
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (direction : Fin (Module.finrank ℝ E))
    (h_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v)
                  i direction) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1
                (smoothToH1Compl_mem_laplacianDomainPow_two
                  (I := I) (M := M) g v))).weak_partial direction y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α
              (smoothToH1Compl_mem_laplacianDomainPow_two
                (I := I) (M := M) g v) direction y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
                (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1
                    (smoothToH1Compl_mem_laplacianDomainPow_two
                      (I := I) (M := M) g v))).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1
                (smoothToH1Compl_mem_laplacianDomainPow_two
                  (I := I) (M := M) g v))).u_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1
                (smoothToH1Compl_mem_laplacianDomainPow_two
                  (I := I) (M := M) g v))).f_chart y * ψ y
          ∂(volume : Measure EuclN))) :
    DiffChartBilinearH1ComplData (I := I) (M := M) g α :=
  diffChartBilinearH1ComplData_of_laplacianDomainPow_two_via_residual
    (I := I) (M := M) g α
    (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v)
    direction
    (memW1p_fChartResidual_smoothToH1Compl (I := I) (M := M) g α v)
    h_identity

noncomputable def smoothFChartResidual
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
    (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v)

omit [NeZero (Module.finrank ℝ E)] in
lemma smoothFChartResidual_memW1p
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (smoothFChartResidual (I := I) (M := M) g α v)
      (chartTargetEuclid (I := I) (M := M) α) := by
  unfold smoothFChartResidual
  exact memW1p_fChartResidual_smoothToH1Compl (I := I) (M := M) g α v

omit [NeZero (Module.finrank ℝ E)] in
lemma smoothFChartResidual_tendsto_fChartResidual_lp_weighted
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (v : ℕ → SmoothScalar g)
    (h_tendsto : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h)) :
    Tendsto (fun n =>
      eLpNorm
        (fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y -
          DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
            (I := I) (M := M) g α u_h y) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
      atTop (𝓝 0) := by
  classical
  have h_residual_tendsto : Tendsto (fun n =>
      DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
        (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n)))
      atTop (𝓝 (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
        (I := I) (M := M) g α u_h)) := by
    set ρα : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α
    set Δρα : C^∞⟮I, M; ℝ⟯ := laplacianOfChartPOU (I := I) (M := M) g α
    have h_A : Tendsto (fun n => -((2 : ℝ) •
        gradInnerCLM (I := I) (M := M) g ρα
          (smoothToH1Compl (I := I) (M := M) g (v n))))
        atTop (𝓝 (-((2 : ℝ) •
          gradInnerCLM (I := I) (M := M) g ρα u_h))) := by
      have h_grad : Tendsto (fun n =>
          gradInnerCLM (I := I) (M := M) g ρα
            (smoothToH1Compl (I := I) (M := M) g (v n)))
          atTop (𝓝 (gradInnerCLM (I := I) (M := M) g ρα u_h)) :=
        ((gradInnerCLM (I := I) (M := M) g ρα).continuous.tendsto _).comp
          h_tendsto
      have h_smul : Tendsto (fun n => (2 : ℝ) •
          gradInnerCLM (I := I) (M := M) g ρα
            (smoothToH1Compl (I := I) (M := M) g (v n)))
          atTop (𝓝 ((2 : ℝ) •
            gradInnerCLM (I := I) (M := M) g ρα u_h)) :=
        Tendsto.const_smul h_grad (2 : ℝ)
      exact h_smul.neg
    have h_B : Tendsto (fun n =>
        smoothMulLp (I := I) (M := M) g Δρα
          (H1ComplToLp (I := I) (M := M) g
            (smoothToH1Compl (I := I) (M := M) g (v n))))
        atTop (𝓝 (smoothMulLp (I := I) (M := M) g Δρα
          (H1ComplToLp (I := I) (M := M) g u_h))) := by
      have h_H1Lp : Tendsto (fun n =>
          H1ComplToLp (I := I) (M := M) g
            (smoothToH1Compl (I := I) (M := M) g (v n)))
          atTop (𝓝 (H1ComplToLp (I := I) (M := M) g u_h)) :=
        ((H1ComplToLp (I := I) (M := M) g).continuous.tendsto _).comp h_tendsto
      exact ((smoothMulLp (I := I) (M := M) g Δρα).continuous.tendsto _).comp h_H1Lp
    have h_sub : Tendsto (fun n =>
        -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g ρα
          (smoothToH1Compl (I := I) (M := M) g (v n))) -
          smoothMulLp (I := I) (M := M) g Δρα
            (H1ComplToLp (I := I) (M := M) g
              (smoothToH1Compl (I := I) (M := M) g (v n))))
        atTop (𝓝 (-((2 : ℝ) • gradInnerCLM (I := I) (M := M) g ρα u_h) -
          smoothMulLp (I := I) (M := M) g Δρα
            (H1ComplToLp (I := I) (M := M) g u_h))) :=
      h_A.sub h_B
    convert h_sub using 1
  have h_chartPulled_tendsto : Tendsto (fun n =>
      chartPushedRawLpFromLp (I := I) (M := M) g α
        (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))))
      atTop (𝓝 (chartPushedRawLpFromLp (I := I) (M := M) g α
        (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α u_h))) :=
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData.chartPushedRawLpFromLp_tendsto
      (I := I) (M := M) g α h_residual_tendsto
  have h_norm_tendsto : Tendsto (fun n =>
      ‖chartPushedRawLpFromLp (I := I) (M := M) g α
        (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
        chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α u_h)‖)
      atTop (𝓝 0) := by
    have h_sub : Tendsto (fun n =>
        chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h))
        atTop (𝓝 0) := by
      have := h_chartPulled_tendsto.sub (tendsto_const_nhds
        (x := chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α u_h)))
      simpa using this
    simpa using (continuous_norm.tendsto (0 :
      Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α)))).comp h_sub
  have h_two_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_eLpNorm_eq : ∀ n,
      eLpNorm
        (((chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h)) : Lp ℝ 2 _) : EuclN → ℝ) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
      ENNReal.ofReal
        ‖chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
        chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α u_h)‖ := by
    intro n
    rw [Lp.norm_def]
    rw [ENNReal.ofReal_toReal
      ((Lp.memLp _).eLpNorm_lt_top.ne)]
  have h_eLp_tendsto : Tendsto (fun n =>
      eLpNorm
        (((chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h)) : Lp ℝ 2 _) : EuclN → ℝ) 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
      atTop (𝓝 0) := by
    have h_funeq : (fun n =>
        eLpNorm
          (((chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
            chartPushedRawLpFromLp (I := I) (M := M) g α
              (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
                (I := I) (M := M) g α u_h)) : Lp ℝ 2 _) : EuclN → ℝ) 2
          ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) =
        fun n => ENNReal.ofReal
          ‖chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h)‖ := by
      funext n
      exact h_eLpNorm_eq n
    rw [h_funeq]
    have h_ofReal_zero : ENNReal.ofReal (0 : ℝ) = 0 := by simp
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 from h_ofReal_zero.symm]
    exact ENNReal.tendsto_ofReal h_norm_tendsto
  have h_subFun_aeEq : ∀ n,
      ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))) -
          chartPushedRawLpFromLp (I := I) (M := M) g α
            (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
              (I := I) (M := M) g α u_h) : Lp ℝ 2 _) : EuclN → ℝ) =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y -
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h y := by
    intro n
    have h_sub_coe :=
      MeasureTheory.Lp.coeFn_sub
        (chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g (v n))))
        (chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α u_h))
    filter_upwards [h_sub_coe] with y hy
    rw [hy]
    rfl
  convert h_eLp_tendsto using 1
  funext n
  exact eLpNorm_congr_ae (h_subFun_aeEq n).symm

omit [NeZero (Module.finrank ℝ E)] in
theorem memW1p_fChartResidual_of_wkpNorm_cauchy_and_lim_eq
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (v : ℕ → SmoothScalar g)
    (_h_conv_H1Compl : Tendsto (fun n => smoothToH1Compl (I := I) (M := M) g (v n))
      atTop (𝓝 u_h))
    (_h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y => smoothFChartResidual (I := I) (M := M) g α (v m) y -
          smoothFChartResidual (I := I) (M := M) g α (v n) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε)
    (h_lim_eq : ∃ F_lim : EuclN → ℝ,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 F_lim
        (chartTargetEuclid (I := I) (M := M) α) ∧
      Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y - F_lim y)
          (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) ∧
      F_lim =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  obtain ⟨F_lim, h_F_lim_w1p, _h_F_lim_tendsto, h_F_lim_aeEq⟩ := h_lim_eq
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    h_F_lim_aeEq).mp h_F_lim_w1p

theorem memW1p_fChartResidual_of_wkpNorm_cauchy_identification
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (v : ℕ → SmoothScalar g)
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y => smoothFChartResidual (I := I) (M := M) g α (v m) y -
          smoothFChartResidual (I := I) (M := M) g α (v n) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε)
    (h_identification : ∀ F_lim : EuclN → ℝ,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 F_lim
        (chartTargetEuclid (I := I) (M := M) α) →
      Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y - F_lim y)
          (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) →
      F_lim =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
        (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_smooth_W1p : ∀ n,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2
        (smoothFChartResidual (I := I) (M := M) g α (v n))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro n
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    exact smoothFChartResidual_memW1p (I := I) (M := M) g α (v n)
  obtain ⟨F_lim, hF_lim_memWkp, hF_lim_tendsto⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.exists_limit_of_wkpNorm_cauchy
      (hΩ_open := chartTargetEuclid_isOpen (I := I) (M := M) α)
      (k := 1) (p := 2) (hp_one := by norm_num) (hp_top := by norm_num)
      (u := fun n => smoothFChartResidual (I := I) (M := M) g α (v n))
      h_smooth_W1p h_cauchy
  have hF_lim_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 F_lim
      (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mp hF_lim_memWkp
  have hF_lim_aeEq := h_identification F_lim hF_lim_W1p hF_lim_tendsto
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    hF_lim_aeEq).mp hF_lim_W1p

noncomputable def diffChartBilinearH1ComplData_of_laplacianDomainPow_two_via_density
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (v : ℕ → SmoothScalar g)
    (h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y => smoothFChartResidual (I := I) (M := M) g α (v m) y -
          smoothFChartResidual (I := I) (M := M) g α (v n) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤ ENNReal.ofReal ε)
    (h_identification : ∀ F_lim : EuclN → ℝ,
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 F_lim
        (chartTargetEuclid (I := I) (M := M) α) →
      Tendsto (fun n =>
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y => smoothFChartResidual (I := I) (M := M) g α (v n) y - F_lim y)
          (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝓝 0) →
      F_lim =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
        DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
          (I := I) (M := M) g α u_h)
    (direction : Fin (Module.finrank ℝ E))
    (h_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i direction) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial direction y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h direction y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j direction y *
                (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).u_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α direction y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
          ∂(volume : Measure EuclN))) :
    DiffChartBilinearH1ComplData (I := I) (M := M) g α :=
  diffChartBilinearH1ComplData_of_laplacianDomainPow_two_via_residual
    (I := I) (M := M) g α hu_h direction
    (memW1p_fChartResidual_of_wkpNorm_cauchy_identification
      (I := I) (M := M) g α hu_h v h_cauchy h_identification)
    h_identity

end DiffChartBilinearH1ComplResidual
end Laplacian
end Analysis
end DifferentialGeometry

end
