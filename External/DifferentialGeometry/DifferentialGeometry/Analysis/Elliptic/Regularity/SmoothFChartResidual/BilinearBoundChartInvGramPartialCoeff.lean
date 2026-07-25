import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplResidual
import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.CLM.ChartFormula
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.StrictCutoffPushforwardBound
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.SmoothMulQuant
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifoldHigherOrder
import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace SmoothFChartResidualBilinearBound

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
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual
open DifferentialGeometry.Analysis.Laplacian.GradInnerCLMChartFormula
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private noncomputable def coefIJ_M
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun x : M =>
    chartStrictCutoff (I := I) (M := M) α x *
      chartInvGramMatrix (I := I) g α x i j *
      partialDeriv (E := E) i
        (scalarOnE (I := I) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
        (extChartAt I α x)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma coefIJ_M_apply (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (x : M) :
    coefIJ_M (I := I) (M := M) g α i j x =
      chartStrictCutoff (I := I) (M := M) α x *
        chartInvGramMatrix (I := I) g α x i j *
        partialDeriv (E := E) i
          (scalarOnE (I := I) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
          (extChartAt I α x) := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma coefIJ_M_eq_zero_off_tsupport_chartStrictCutoff
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : M}
    (hx : chartStrictCutoff (I := I) (M := M) α x = 0) :
    coefIJ_M (I := I) (M := M) g α i j x = 0 := by
  unfold coefIJ_M
  rw [hx]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma coefIJ_M_smooth
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (coefIJ_M (I := I) (M := M) g α i j) := by
  classical
  intro x₀
  by_cases hx_src : x₀ ∈ (chartAt H α).source
  · have h_chart_src_open : IsOpen ((chartAt H α).source) :=
      (chartAt H α).open_source
    have h_cut_smooth : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (chartStrictCutoff (I := I) (M := M) α) x₀ :=
      (chartStrictCutoff_contMDiff (I := I) (M := M) α).contMDiffAt
    have hbase : x₀ ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx_src
    have h_invGram_on : ContMDiffOn I 𝓘(ℝ) ∞
        (fun x : M => chartInvGramMatrix (I := I) g α x i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
    have h_base_open : IsOpen ((trivializationAt E (TangentSpace I) α).baseSet) := by
      rw [trivializationAt_baseSet_eq_chartAt_source]; exact h_chart_src_open
    have h_invGram_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => chartInvGramMatrix (I := I) g α x i j) x₀ := by
      have h := (h_invGram_on x₀ hbase).contMDiffAt
        (h_base_open.mem_nhds hbase)
      exact h
    have hα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
    have h_scalarOnE_contDiffOn : ContDiffOn ℝ ∞
        (scalarOnE (I := I) α
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
        (extChartAt I α).target :=
      DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_contDiffOn
        (I := I) α hα_smooth
    have h_target_open : IsOpen ((extChartAt I α).target) :=
      isOpen_extChartAt_target (I := I) α
    have h_partial_contDiffOn : ContDiffOn ℝ ∞
        (fun y : E => partialDeriv (E := E) i
          (scalarOnE (I := I) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y)
        (extChartAt I α).target := by
      unfold partialDeriv
      have h_fderiv_smooth :
          ContDiffOn ℝ ∞ (fun y : E => fderiv ℝ
            (scalarOnE (I := I) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y)
            (extChartAt I α).target := by
        have h_le : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
          rw [show ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ((⊤ : ℕ∞) : WithTop ℕ∞) from by simp]
        exact h_scalarOnE_contDiffOn.fderiv_of_isOpen h_target_open h_le
      exact h_fderiv_smooth.clm_apply contDiffOn_const
    have hx_target : extChartAt I α x₀ ∈ (extChartAt I α).target := by
      have hx_ext_src : x₀ ∈ (extChartAt I α).source := by
        rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_src
      exact (extChartAt I α).map_source hx_ext_src
    have h_partial_at_E : ContDiffAt ℝ ∞
        (fun y : E => partialDeriv (E := E) i
          (scalarOnE (I := I) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y)
        (extChartAt I α x₀) := by
      have h_within := h_partial_contDiffOn (extChartAt I α x₀) hx_target
      exact h_within.contDiffAt (h_target_open.mem_nhds hx_target)
    have h_extChart_contMDiff : ContMDiffAt I 𝓘(ℝ, E) ∞
        (extChartAt I α) x₀ := by
      have h_open_src : IsOpen ((chartAt H α).source) := (chartAt H α).open_source
      have h_on : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
        contMDiffOn_extChartAt (I := I) (x := α)
      exact (h_on x₀ hx_src).contMDiffAt (h_open_src.mem_nhds hx_src)
    have h_partial_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun x : M => partialDeriv (E := E) i
          (scalarOnE (I := I) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
          (extChartAt I α x)) x₀ := by
      have h_partial_at_E_mDiff : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
          (fun y : E => partialDeriv (E := E) i
            (scalarOnE (I := I) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y)
          (extChartAt I α x₀) :=
        (contMDiffAt_iff_contDiffAt).mpr h_partial_at_E
      exact h_partial_at_E_mDiff.comp _ h_extChart_contMDiff
    unfold coefIJ_M
    exact (h_cut_smooth.mul h_invGram_at).mul h_partial_at
  · have hx_compl : x₀ ∈ ((chartAt H α).source)ᶜ := hx_src
    have h_ev_zero : ∀ᶠ x in 𝓝 x₀,
        chartStrictCutoff (I := I) (M := M) α x = 0 := by
      have h_ev_nhdsSet :=
        chartStrictCutoff_eventually_zero_nhdsSet_compl_source (I := I) (M := M) α
      exact h_ev_nhdsSet.filter_mono (nhds_le_nhdsSet hx_compl)
    have h_ev_zero_coef : ∀ᶠ x in 𝓝 x₀,
        coefIJ_M (I := I) (M := M) g α i j x = 0 := by
      filter_upwards [h_ev_zero] with x hx
      exact coefIJ_M_eq_zero_off_tsupport_chartStrictCutoff (I := I) (M := M)
        g α i j hx
    have h_const : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (0 : ℝ)) x₀ :=
      contMDiffAt_const
    have h_evEq : coefIJ_M (I := I) (M := M) g α i j =ᶠ[𝓝 x₀]
        (fun _ : M => (0 : ℝ)) := h_ev_zero_coef
    exact h_const.congr_of_eventuallyEq h_evEq

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma tsupport_coefIJ_M_subset
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    tsupport (coefIJ_M (I := I) (M := M) g α i j) ⊆ (chartAt H α).source := by
  classical
  have h_supp_subset : Function.support (coefIJ_M (I := I) (M := M) g α i j) ⊆
      Function.support (chartStrictCutoff (I := I) (M := M) α) := by
    intro x hx
    by_contra hxoff
    apply hx
    have h0 : chartStrictCutoff (I := I) (M := M) α x = 0 := by
      simpa [Function.mem_support, not_not] using hxoff
    exact coefIJ_M_eq_zero_off_tsupport_chartStrictCutoff (I := I) (M := M)
      g α i j h0
  have h_tsupp_subset : tsupport (coefIJ_M (I := I) (M := M) g α i j) ⊆
      tsupport (chartStrictCutoff (I := I) (M := M) α) :=
    closure_minimal (h_supp_subset.trans (subset_tsupport _))
      (isClosed_tsupport _)
  exact h_tsupp_subset.trans (chartStrictCutoff_tsupport_subset (I := I) (M := M) α)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartPushedRaw_coefIJ_M_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
        (coefIJ_M (I := I) (M := M) g α i j) y =
      chartStrictCutoff (I := I) (M := M) α
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) *
        invGramOnEuclid (I := I) g α i j y *
        partialDerivOnEuclid (I := I) (M := M) α i
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y := by
  classical
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (coefIJ_M (I := I) (M := M) g α i j) hy]
  unfold coefIJ_M
  have h_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy; exact hy
  have h_φx_eq : extChartAt I α ((extChartAt I α).symm
        ((toEuclidean (E := E)).symm y)) =
      (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv h_tgt
  rw [h_φx_eq]
  unfold partialDerivOnEuclid invGramOnEuclid
  rfl

end SmoothFChartResidualBilinearBound
end Laplacian
end Analysis
end DifferentialGeometry

end
