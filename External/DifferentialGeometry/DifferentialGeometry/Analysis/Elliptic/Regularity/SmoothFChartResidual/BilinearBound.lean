import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplResidual
import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.CLM.ChartFormula
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.StrictCutoffPushforwardBound
import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.SmoothMulQuant
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifoldHigherOrder
import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBoundSmoothRepPieces
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBoundChartInvGramPartialCoeff
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBoundGradInnerCoeffExtension
import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothFChartResidual.BilinearBoundChartPushedPartialDeriv


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

private lemma wkpNorm_chartPushedRaw_lapPiece_le_etaTimesV_aux
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (chartPushedRaw (I := I) (M := M) α
            (etaTimesV (I := I) (M := M) α v.toFun))
          (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  obtain ⟨b, hb_smooth, _, hb_one_on_tsupp, hb_supp⟩ :=
    exists_chart_cutoff_M (I := I) (M := M) α
  set bΔρα : M → ℝ := fun x : M =>
    b x * (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x with hbΔρα_def
  have hbΔρα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ bΔρα :=
    hb_smooth.mul (laplacianOfChartPOU (I := I) (M := M) g α).contMDiff
  have hbΔρα_supp : tsupport bΔρα ⊆ (chartAt H α).source := by
    have h_eq : bΔρα = (fun x : M => b x •
      (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x) := by
      funext x; rfl
    rw [h_eq]
    exact (tsupport_smul_subset_left (f := b)
      (g := ((laplacianOfChartPOU (I := I) (M := M) g α : C^∞⟮I, M; ℝ⟯) : M → ℝ))).trans
      hb_supp
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    smoothExtensionScalar_iteratedFDeriv_bound (I := I) (M := M) α
      hbΔρα_smooth hbΔρα_supp 1
  set Λ : EuclN → ℝ := smoothExtensionScalar (I := I) (M := M) α bΔρα with hΛ_def
  have hΛ_smooth : ContDiff ℝ (⊤ : ℕ∞) Λ :=
    contDiff_smoothExtensionScalar (I := I) (M := M) α hbΔρα_smooth hbΔρα_supp
  have hΛ_bound : ∀ j ≤ 1, ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      ‖iteratedFDeriv ℝ j Λ y‖ ≤ C := fun j hj y _ => hC_bound j hj y
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le
      (d := Module.finrank ℝ E) 1 (p := 2) (by norm_num) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      hΛ_smooth hC_nn hΛ_bound
  refine ⟨K, hK_pos, ?_⟩
  intro v
  have h_factor : (fun y : EuclN => chartPushedRaw (I := I) (M := M) α
        (lapPiece (I := I) (M := M) g α v.toFun) y) =ᵐ[
        volume.restrict (chartTargetEuclid (I := I) (M := M) α)]
      fun y : EuclN => Λ y * chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun) y := by
    refine (MeasureTheory.ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    exact chartPushedRaw_lapPiece_factor (I := I) (M := M) g α v.toFun
      hb_one_on_tsupp hy
  have h_norm_eq :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y : EuclN => Λ y * chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_factor
  rw [h_norm_eq]
  have hH_W12 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (etaTimesV (I := I) (M := M) α v.toFun) :=
      etaTimesV_smooth (I := I) (M := M) α v.smooth
    have h_supp : tsupport (etaTimesV (I := I) (M := M) α v.toFun) ⊆
        (chartAt H α).source :=
      tsupport_etaTimesV_subset (I := I) (M := M) α v.toFun
    have h_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) :=
      DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualMemW1p.memW1p_chartPushedRaw_of_contMDiff_tsupport
        (I := I) (M := M) (α := α) h_smooth h_supp 2
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mpr h_w1p
  exact hK_bound hH_W12

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma Λgrad_apply_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    Λgrad (I := I) (M := M) g α i y =
      gradInnerCoefI_M (I := I) (M := M) g α i
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
  unfold Λgrad
  have h_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy; exact hy
  classical
  change (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
      gradInnerCoefI_M (I := I) (M := M) g α i
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    else 0) = _
  rw [if_pos h_tgt]

omit [NeZero (Module.finrank ℝ E)] in
private lemma Λgrad_iteratedFDeriv_bound
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ 1, ∀ y : EuclN,
      ‖iteratedFDeriv ℝ j (Λgrad (I := I) (M := M) g α i) y‖ ≤ C := by
  unfold Λgrad
  exact smoothExtensionScalar_iteratedFDeriv_bound (I := I) (M := M) α
    (gradInnerCoefI_M_smooth (I := I) (M := M) g α i)
    (tsupport_gradInnerCoefI_M_subset (I := I) (M := M) g α i) 1

omit [NeZero (Module.finrank ℝ E)] in
lemma chartPushedRaw_gradInnerPiece_eq_sum
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun) y =
      (2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
        Λgrad (I := I) (M := M) g α i y *
          partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun) y := by
  classical
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (gradInnerPiece (I := I) (M := M) g α v.toFun) hy]
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hx_def
  rw [gradInnerPiece_apply]
  have h_tgt : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy; exact hy
  have hx_src : x ∈ (chartAt H α).source := by
    have hsrc : x ∈ (extChartAt I α).source := (extChartAt I α).map_target h_tgt
    rwa [extChartAt_source_eq_chartAt_source (I := I)] at hsrc
  have hx_base : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hx_src
  have hx_int : extChartAt I α x ∈ interior (extChartAt I α).target := by
    have h_φx : extChartAt I α x = (toEuclidean (E := E)).symm y := by
      rw [hx_def]; exact (extChartAt I α).right_inv h_tgt
    rw [h_φx]
    exact extChartAt_target_subset_interior_of_boundaryless (I := I) α h_tgt
  have hηv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (etaTimesV (I := I) (M := M) α v.toFun) :=
    etaTimesV_smooth (I := I) (M := M) α v.smooth
  have hα_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
  have hgradFun_decomp : gradFun (I := I) g
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x =
      ∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x •
          chartBasisVecFiber (I := I) α i x := by
    have hα_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
      hα_smooth.mdifferentiableAt (by simp)
    have h := gradChartLocal_eq_gradFun (I := I) g (α := α)
      hα_mdiff hx_base hx_int
    rw [← h]; rfl
  have h_mfderiv_apply : ∀ i : Fin (Module.finrank ℝ E),
      mfderiv I 𝓘(ℝ, ℝ) (etaTimesV (I := I) (M := M) α v.toFun) x
          (chartBasisVecFiber (I := I) α i x) =
      partialDeriv (E := E) i
        (scalarOnE (I := I) α (etaTimesV (I := I) (M := M) α v.toFun))
        (extChartAt I α x) := fun i =>
    mfderiv_chartBasisVecFiber (I := I) (α := α) hηv_smooth hx_src hx_int i
  have h_inner_eq :
      g.inner x (gradFun (I := I) g
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
          (gradFun (I := I) g (etaTimesV (I := I) (M := M) α v.toFun) x) =
      mfderiv I 𝓘(ℝ, ℝ) (etaTimesV (I := I) (M := M) α v.toFun) x
        (gradFun (I := I) g
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
    rw [g.symm x _ _]
    exact inner_gradFun (I := I) g
      (etaTimesV (I := I) (M := M) α v.toFun) x _
  rw [h_inner_eq, hgradFun_decomp]
  set L : TangentSpace I x →L[ℝ] ℝ :=
    mfderiv I 𝓘(ℝ, ℝ) (etaTimesV (I := I) (M := M) α v.toFun) x with hL_def
  have h_mfderiv_sum : L
      (∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x •
          chartBasisVecFiber (I := I) α i x) =
      ∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x *
          L (chartBasisVecFiber (I := I) α i x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_smul, smul_eq_mul]
  have h_LHS_eq : (2 : ℝ) * L
      (∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x •
          chartBasisVecFiber (I := I) α i x) =
    (2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x *
          L (chartBasisVecFiber (I := I) α i x) := by
    rw [h_mfderiv_sum]
  have h_mfderiv_apply_L : ∀ i : Fin (Module.finrank ℝ E),
      L (chartBasisVecFiber (I := I) α i x) =
      partialDeriv (E := E) i
        (scalarOnE (I := I) α (etaTimesV (I := I) (M := M) α v.toFun))
        (extChartAt I α x) := by
    intro i
    rw [hL_def]
    exact h_mfderiv_apply i
  change (2 : ℝ) * L _ = _
  rw [h_LHS_eq]
  simp_rw [h_mfderiv_apply_L]
  have hΛ_apply : ∀ i : Fin (Module.finrank ℝ E),
      Λgrad (I := I) (M := M) g α i y =
        chartStrictCutoff (I := I) (M := M) α x *
          gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x := by
    intro i
    rw [Λgrad_apply_of_mem (I := I) (M := M) g α i hy]
    rfl
  have h_partialDerivOnEuclid_apply : ∀ i : Fin (Module.finrank ℝ E),
      partialDerivOnEuclid (I := I) (M := M) α i
          (etaTimesV (I := I) (M := M) α v.toFun) y =
        partialDeriv (E := E) i
          (scalarOnE (I := I) α
            (etaTimesV (I := I) (M := M) α v.toFun))
          (extChartAt I α x) := by
    intro i
    have hφx_eq : extChartAt I α x = (toEuclidean (E := E)).symm y := by
      rw [hx_def]; exact (extChartAt I α).right_inv h_tgt
    rw [hφx_eq]; rfl
  simp_rw [hΛ_apply, h_partialDerivOnEuclid_apply]
  have h_sum_eq :
      ∑ i : Fin (Module.finrank ℝ E),
        gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x *
          partialDeriv (E := E) i
            (scalarOnE (I := I) α
              (etaTimesV (I := I) (M := M) α v.toFun))
            (extChartAt I α x) =
      ∑ i : Fin (Module.finrank ℝ E),
        (chartStrictCutoff (I := I) (M := M) α x *
          gradChartCoeff (I := I) g α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x) *
          partialDeriv (E := E) i
            (scalarOnE (I := I) α
              (etaTimesV (I := I) (M := M) α v.toFun))
            (extChartAt I α x) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h_grad_zero : gradChartCoeff (I := I) g α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) i x = 0
    · rw [h_grad_zero]; ring
    · have hx_supp : x ∈ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
        by_contra hx_off
        apply h_grad_zero
        have h_open : IsOpen
            (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))ᶜ :=
          (isClosed_tsupport _).isOpen_compl
        have h_ev : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 x]
            (fun _ : M => (0 : ℝ)) := by
          filter_upwards [h_open.mem_nhds hx_off] with z hz
          by_contra hne
          exact hz (subset_tsupport _ hne)
        unfold gradChartCoeff
        refine Finset.sum_eq_zero (fun j _ => ?_)
        have h_scalar_ev : scalarOnE (I := I) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) =ᶠ[𝓝 (extChartAt I α x)]
            (fun _ : E => (0 : ℝ)) := by
          have h_target_open : IsOpen ((extChartAt I α).target) :=
            isOpen_extChartAt_target (I := I) α
          have h_open_target : (extChartAt I α).target ∈ 𝓝 (extChartAt I α x) := by
            have h_ext_src : x ∈ (extChartAt I α).source := by
              rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_src
            exact h_target_open.mem_nhds ((extChartAt I α).map_source h_ext_src)
          have h_symm_cont : ContinuousAt (extChartAt I α).symm (extChartAt I α x) := by
            have h_continuousOn := continuousOn_extChartAt_symm (I := I) α
            have h_target_mem : extChartAt I α x ∈ (extChartAt I α).target := by
              have h_ext_src : x ∈ (extChartAt I α).source := by
                rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_src
              exact (extChartAt I α).map_source h_ext_src
            exact (h_continuousOn _ h_target_mem).continuousAt h_open_target
          have h_left_inv : ∀ᶠ z in 𝓝 (extChartAt I α x),
              (extChartAt I α) ((extChartAt I α).symm z) = z := by
            filter_upwards [h_open_target] with z hz
            exact (extChartAt I α).right_inv hz
          have h_symm_x : (extChartAt I α).symm (extChartAt I α x) = x := by
            have h_ext_src : x ∈ (extChartAt I α).source := by
              rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_src
            exact (extChartAt I α).left_inv h_ext_src
          have h_ev_through_symm : ∀ᶠ z in 𝓝 (extChartAt I α x),
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)
                ((extChartAt I α).symm z) = 0 := by
            have h_pre : (extChartAt I α).symm ⁻¹' {x : M | ((chartAtlasPOU I M α
                : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0} ∈ 𝓝 (extChartAt I α x) := by
              have h_set_open : {x : M | ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0}
                  ∈ 𝓝 x := h_ev
              exact h_symm_cont.preimage_mem_nhds (by rwa [h_symm_x])
            filter_upwards [h_pre] with z hz using hz
          filter_upwards [h_ev_through_symm] with z hz using hz
        have h_partial_zero :
            partialDeriv (E := E) j (scalarOnE (I := I) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
              (extChartAt I α x) = 0 := by
          unfold partialDeriv
          rw [Filter.EventuallyEq.fderiv_eq h_scalar_ev]
          simp
        rw [h_partial_zero]; ring
      have h_cut : chartStrictCutoff (I := I) (M := M) α x = 1 :=
        chartStrictCutoff_eq_one_on_tsupport_chartAtlasPOU (I := I) (M := M) α hx_supp
      rw [h_cut]; ring
  rw [h_sum_eq]

section HeadlineAssembly

omit [NeZero (Module.finrank ℝ E)] in
lemma smoothRep_contMDiff (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (smoothRep (I := I) (M := M) g α v) := by
  rw [smoothRep_eq_pieces (I := I) (M := M) g α v]
  exact ((gradInnerPiece_smooth (I := I) (M := M) g α v).neg).sub
    (lapPiece_smooth (I := I) (M := M) g α v)

omit [NeZero (Module.finrank ℝ E)] in
lemma tsupport_smoothRep_subset_source
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    tsupport (smoothRep (I := I) (M := M) g α v) ⊆ (chartAt H α).source := by
  classical
  have h_eq := smoothRep_eq_pieces (I := I) (M := M) g α v
  have h_supp_sub : Function.support (smoothRep (I := I) (M := M) g α v) ⊆
      tsupport (gradInnerPiece (I := I) (M := M) g α v.toFun) ∪
        tsupport (lapPiece (I := I) (M := M) g α v.toFun) := by
    intro x hx
    by_contra hx_off
    apply hx
    rw [h_eq]
    have h_or : ¬ (x ∈ tsupport (gradInnerPiece (I := I) (M := M) g α v.toFun) ∨
        x ∈ tsupport (lapPiece (I := I) (M := M) g α v.toFun)) := hx_off
    have h_and : x ∉ tsupport (gradInnerPiece (I := I) (M := M) g α v.toFun) ∧
        x ∉ tsupport (lapPiece (I := I) (M := M) g α v.toFun) := not_or.mp h_or
    obtain ⟨h1, h2⟩ := h_and
    have h_grad_zero : gradInnerPiece (I := I) (M := M) g α v.toFun x = 0 := by
      by_contra hne
      exact h1 (subset_tsupport _ hne)
    have h_lap_zero : lapPiece (I := I) (M := M) g α v.toFun x = 0 := by
      by_contra hne
      exact h2 (subset_tsupport _ hne)
    change -gradInnerPiece (I := I) (M := M) g α v.toFun x -
        lapPiece (I := I) (M := M) g α v.toFun x = 0
    rw [h_grad_zero, h_lap_zero]; ring
  have h_tsupp_sub : tsupport (smoothRep (I := I) (M := M) g α v) ⊆
      tsupport (gradInnerPiece (I := I) (M := M) g α v.toFun) ∪
        tsupport (lapPiece (I := I) (M := M) g α v.toFun) :=
    closure_minimal h_supp_sub
      ((isClosed_tsupport _).union (isClosed_tsupport _))
  refine h_tsupp_sub.trans (Set.union_subset ?_ ?_)
  · exact tsupport_gradInnerPiece_subset_source (I := I) (M := M) g α v.toFun
  · exact tsupport_lapPiece_subset_source (I := I) (M := M) g α v.toFun

omit [NeZero (Module.finrank ℝ E)] in
lemma smoothFChartResidual_ae_eq_chartPushedRaw_smoothRep
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
        (I := I) (M := M) g α v =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedRaw (I := I) (M := M) α
        (smoothRep (I := I) (M := M) g α v) := by
  classical
  unfold DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
  unfold DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fChartResidual
  have h_lp_ae := DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualMemW1p.fHLeibnizResidualLp_smoothToH1Compl_coeFn_ae
    (I := I) (M := M) g α v
  have h_fChart_ae := chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α
    (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
      (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v))
  have h_lp_meas : Measurable
      ((DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
          (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v) :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have h_rep_meas : Measurable (smoothRep (I := I) (M := M) g α v) :=
    (smoothRep_contMDiff (I := I) (M := M) g α v).continuous.measurable
  have h_smoothRep_eq_fHRep :
      DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualMemW1p.fHLeibnizResidualSmoothRep
        (I := I) (M := M) g α v = smoothRep (I := I) (M := M) g α v := by
    funext x
    rfl
  rw [h_smoothRep_eq_fHRep] at h_lp_ae
  have h_chartPushed_lp_ae :=
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData.chartPushedRaw_aeEq_of_aeEq
      (I := I) (M := M) g α h_lp_meas h_rep_meas h_lp_ae
  have h_fChart_smooth_ae :
      ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl.fHLeibnizResidualLp
            (I := I) (M := M) g α (smoothToH1Compl (I := I) (M := M) g v)) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        chartPushedRaw (I := I) (M := M) α
          (smoothRep (I := I) (M := M) g α v) :=
    h_fChart_ae.trans h_chartPushed_lp_ae
  have h_vol_abs_weighted : (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro A hA
    have h_chartTarget_meas : MeasurableSet
        (chartTargetEuclid (I := I) (M := M) α) :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
    unfold chartPulledWeightedMeasure at hA
    rw [show ((volume : Measure EuclN).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
        (chartTargetEuclid (I := I) (M := M) α) =
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      from MeasureTheory.restrict_withDensity h_chartTarget_meas _] at hA
    rw [MeasureTheory.withDensity_apply_eq_zero'
      (μ := (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      (ENNReal.measurable_ofReal.comp_aemeasurable
        ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_chartTarget_meas))]
      at hA
    rw [Measure.restrict_apply' h_chartTarget_meas]
    rw [Measure.restrict_apply' h_chartTarget_meas] at hA
    refine MeasureTheory.measure_mono_null ?_ hA
    intro y ⟨hy_A, hy_chart⟩
    refine ⟨⟨?_, hy_A⟩, hy_chart⟩
    have h_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α hy_chart
    exact (ENNReal.ofReal_pos.mpr h_pos).ne'
  exact h_vol_abs_weighted.ae_le h_fChart_smooth_ae

omit [NeZero (Module.finrank ℝ E)] in
private lemma memWkp_chartPushedRaw_smoothRep
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (chartPushedRaw (I := I) (M := M) α
        (smoothRep (I := I) (M := M) g α v))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_w1p :=
    DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualMemW1p.memW1p_chartPushedRaw_of_contMDiff_tsupport
      (I := I) (M := M) (f := smoothRep (I := I) (M := M) g α v) (α := α)
      (smoothRep_contMDiff (I := I) (M := M) g α v)
      (tsupport_smoothRep_subset_source (I := I) (M := M) g α v) 2
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mpr h_w1p

omit [NeZero (Module.finrank ℝ E)] in
lemma chartPushedRaw_smoothRep_eq
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) (y : EuclN) :
    chartPushedRaw (I := I) (M := M) α
        (smoothRep (I := I) (M := M) g α v) y =
      -chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y -
        chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y := by
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy,
        chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    rw [smoothRep_eq_pieces (I := I) (M := M) g α v]
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy,
        chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
    ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma memWkp_chartPushedRaw_etaTimesV
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hηv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (etaTimesV (I := I) (M := M) α v.toFun) :=
    etaTimesV_smooth (I := I) (M := M) α v.smooth
  have hηv_supp : tsupport (etaTimesV (I := I) (M := M) α v.toFun) ⊆
      (chartAt H α).source :=
    tsupport_etaTimesV_subset (I := I) (M := M) α v.toFun
  have hCP_smooth : ContDiff ℝ ∞
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun)) :=
    chartPushedRaw_contDiff (I := I) (M := M) hηv_smooth hηv_supp
  have hCP_cpt : HasCompactSupport
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun)) :=
    chartPushedRaw_smooth_hasCompactSupport_local (I := I) (M := M) hηv_supp
  have hCP_tsupp : tsupport (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun)) ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    tsupport_chartPushedRaw_subset_chartTargetEuclid (I := I) (M := M) hηv_supp
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_of_smooth_compactSupport
    (d := Module.finrank ℝ E)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (by exact hCP_smooth) hCP_cpt hCP_tsupp (by norm_num : (1 : ℝ≥0∞) ≤ 2) 2

omit [NeZero (Module.finrank ℝ E)] in
private lemma memWkp_partialDerivOnEuclid_etaTimesV
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (i : Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (partialDerivOnEuclid (I := I) (M := M) α i
        (etaTimesV (I := I) (M := M) α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
  have hηv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (etaTimesV (I := I) (M := M) α v.toFun) :=
    etaTimesV_smooth (I := I) (M := M) α v.smooth
  have hηv_supp : tsupport (etaTimesV (I := I) (M := M) α v.toFun) ⊆
      (chartAt H α).source :=
    tsupport_etaTimesV_subset (I := I) (M := M) α v.toFun
  have h_chartPushed_W22 := memWkp_chartPushedRaw_etaTimesV (I := I) (M := M) g α v
  have h_chosen_mem :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 i
          (chartPushedRaw (I := I) (M := M) α
            (etaTimesV (I := I) (M := M) α v.toFun))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.chosenWeakPartial_mem
      h_chartPushed_W22 i
  have h_ae := partialDerivOnEuclid_ae_eq_chosenWeakPartial
    (I := I) (M := M) (α := α) (i := i) hηv_smooth hηv_supp
    (p := (2 : ℝ≥0∞)) (by norm_num)
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_congr_ae
    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae).mpr h_chosen_mem

private lemma wkpNorm_chartPushedRaw_etaTimesV_le
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 2 2
        (chartPushedRaw (I := I) (M := M) α
          (etaTimesV (I := I) (M := M) α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) g 2 2
        (fun x : M => v.toFun x) := by
  classical
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNorm_chartPushedRaw_strictCutoff_mul_le
      (I := I) (M := M) g α 2 (p := 2) (by norm_num) (by norm_num)
  refine ⟨C, hC_pos, ?_⟩
  intro v
  have h_v_MemWkpChart : MemWkpChart (I := I) (M := M) g 2 2 v.toFun :=
    memWkpChart_of_contMDiff_k (I := I) (M := M) g (by norm_num) 2 v.smooth
  have h_funext : etaTimesV (I := I) (M := M) α v.toFun =
      fun x : M => chartStrictCutoff (I := I) (M := M) α x * v.toFun x := by
    funext x; rfl
  rw [h_funext]
  exact hC_bound h_v_MemWkpChart

private lemma wkpNorm_partialDerivOnEuclid_etaTimesV_le
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      ∀ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun))
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal C * wkpNormChart (I := I) (M := M) g 2 2
          (fun x : M => v.toFun x) := by
  classical
  have h_per_i_partial : ∀ i : Fin (Module.finrank ℝ E), ∃ C_p : ℝ, 0 < C_p ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u → tsupport u ⊆ (chartAt H α).source →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (partialDerivOnEuclid (I := I) (M := M) α i u)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal C_p *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 2 2
            (chartPushedRaw (I := I) (M := M) α u)
            (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    wkpNorm_partialDerivOnEuclid_le_wkpNorm_chartPushedRaw_succ
      (I := I) (M := M) α i 1 (p := 2) (by norm_num) (by norm_num)
  let Cp : Fin (Module.finrank ℝ E) → ℝ := fun i => (h_per_i_partial i).choose
  have hCp_pos : ∀ i, 0 < Cp i := fun i => (h_per_i_partial i).choose_spec.1
  have hCp_bound : ∀ i : Fin (Module.finrank ℝ E),
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u → tsupport u ⊆ (chartAt H α).source →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (partialDerivOnEuclid (I := I) (M := M) α i u)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal (Cp i) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 2 2
            (chartPushedRaw (I := I) (M := M) α u)
            (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    (h_per_i_partial i).choose_spec.2
  obtain ⟨C_strict, hC_strict_pos, hC_strict_bound⟩ :=
    wkpNorm_chartPushedRaw_etaTimesV_le (I := I) (M := M) g α
  by_cases h_fin_zero : Module.finrank ℝ E = 0
  · exact absurd h_fin_zero (NeZero.ne _)
  have h_fin_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero h_fin_zero
  haveI h_nonempty : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, h_fin_pos⟩⟩
  set Cmax : ℝ := Finset.univ.sup' (Finset.univ_nonempty (α := Fin _)) Cp
  have hCmax_ge : ∀ i, Cp i ≤ Cmax := fun i => Finset.le_sup' Cp (Finset.mem_univ i)
  have hCmax_pos : 0 < Cmax :=
    lt_of_lt_of_le (hCp_pos h_nonempty.some) (hCmax_ge h_nonempty.some)
  set C_total : ℝ := Cmax * C_strict with hC_total_def
  have hC_total_pos : 0 < C_total := mul_pos hCmax_pos hC_strict_pos
  refine ⟨C_total, hC_total_pos, ?_⟩
  intro v i
  have hηv_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (etaTimesV (I := I) (M := M) α v.toFun) :=
    etaTimesV_smooth (I := I) (M := M) α v.smooth
  have hηv_supp : tsupport (etaTimesV (I := I) (M := M) α v.toFun) ⊆
      (chartAt H α).source :=
    tsupport_etaTimesV_subset (I := I) (M := M) α v.toFun
  have h_partial_bound := hCp_bound i hηv_smooth hηv_supp
  have h_strict_bound := hC_strict_bound v
  calc DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (partialDerivOnEuclid (I := I) (M := M) α i
          (etaTimesV (I := I) (M := M) α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal (Cp i) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 2 2
            (chartPushedRaw (I := I) (M := M) α
              (etaTimesV (I := I) (M := M) α v.toFun))
            (chartTargetEuclid (I := I) (M := M) α) := h_partial_bound
    _ ≤ ENNReal.ofReal (Cp i) *
            (ENNReal.ofReal C_strict * wkpNormChart (I := I) (M := M) g 2 2 v.toFun) := by
            exact mul_le_mul_of_nonneg_left h_strict_bound (zero_le _)
    _ = ENNReal.ofReal (Cp i * C_strict) *
            wkpNormChart (I := I) (M := M) g 2 2 v.toFun := by
            rw [← mul_assoc, ENNReal.ofReal_mul (hCp_pos i).le]
    _ ≤ ENNReal.ofReal C_total *
            wkpNormChart (I := I) (M := M) g 2 2 v.toFun := by
            refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hC_total_def]
            exact mul_le_mul_of_nonneg_right (hCmax_ge i) hC_strict_pos.le

private lemma wkpNorm_chartPushedRaw_gradInnerPiece_le
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) g 2 2
        (fun x : M => v.toFun x) := by
  classical
  have h_per_i_smul : ∀ i : Fin (Module.finrank ℝ E), ∃ K : ℝ, 0 < K ∧
      ∀ {u : EuclN → ℝ},
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 2 u
          (chartTargetEuclid (I := I) (M := M) α) →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y => Λgrad (I := I) (M := M) g α i y * u y)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal K *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 2 u
            (chartTargetEuclid (I := I) (M := M) α) := by
    intro i
    obtain ⟨C_Λ, hC_Λ_nn, hC_Λ_bound⟩ :=
      Λgrad_iteratedFDeriv_bound (I := I) (M := M) g α i
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le
      (d := Module.finrank ℝ E) 1 (p := 2) (by norm_num) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (Λgrad_contDiff (I := I) (M := M) g α i)
      hC_Λ_nn (fun j hj y _ => hC_Λ_bound j hj y)
  let K : Fin (Module.finrank ℝ E) → ℝ := fun i => (h_per_i_smul i).choose
  have hK_pos : ∀ i, 0 < K i := fun i => (h_per_i_smul i).choose_spec.1
  have hK_bound : ∀ i : Fin (Module.finrank ℝ E),
      ∀ {u : EuclN → ℝ},
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 2 u
          (chartTargetEuclid (I := I) (M := M) α) →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y => Λgrad (I := I) (M := M) g α i y * u y)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal (K i) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 2 u
            (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    (h_per_i_smul i).choose_spec.2
  obtain ⟨C_partial, hC_partial_pos, hC_partial_bound⟩ :=
    wkpNorm_partialDerivOnEuclid_etaTimesV_le (I := I) (M := M) g α
  set sumK : ℝ := ∑ i : Fin (Module.finrank ℝ E), K i with hsumK_def
  have hsumK_nn : 0 ≤ sumK :=
    Finset.sum_nonneg (fun i _ => (hK_pos i).le)
  set Cfinal : ℝ := 2 * (sumK * C_partial) + 1 with hCfinal_def
  have h_Cfinal_pos : 0 < Cfinal := by
    rw [hCfinal_def]; linarith [mul_nonneg hsumK_nn hC_partial_pos.le]
  refine ⟨Cfinal, h_Cfinal_pos, ?_⟩
  intro v
  have h_pointwise : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y =
        (2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
          Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y := fun y hy =>
    chartPushedRaw_gradInnerPiece_eq_sum (I := I) (M := M) g α v hy
  have h_ae : (chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun)) =ᵐ[
        volume.restrict (chartTargetEuclid (I := I) (M := M) α)]
      fun y => (2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
        Λgrad (I := I) (M := M) g α i y *
          partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun) y := by
    refine (MeasureTheory.ae_restrict_iff'
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy; exact h_pointwise y hy
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
        (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae]
  have h_partial_mem : ∀ i : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2
        (partialDerivOnEuclid (I := I) (M := M) α i
          (etaTimesV (I := I) (M := M) α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) := fun i =>
    memWkp_partialDerivOnEuclid_etaTimesV (I := I) (M := M) g α v i
  have h_summand_mem : ∀ i : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2
        (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
          partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro i
    obtain ⟨C_Λ, hC_Λ_nn, hC_Λ_bound⟩ :=
      Λgrad_iteratedFDeriv_bound (I := I) (M := M) g α i
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.smul_smooth_bounded
      (d := Module.finrank ℝ E) 1 (p := 2) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (Λgrad_contDiff (I := I) (M := M) g α i)
      (fun j hj y _ => hC_Λ_bound j hj y)
      (h_partial_mem i)
  have h_sum_mem_gen : ∀ (S : Finset (Fin (Module.finrank ℝ E))),
      (∀ ε ∈ S, DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2
        (fun y : EuclN => Λgrad (I := I) (M := M) g α ε y *
          partialDerivOnEuclid (I := I) (M := M) α ε
            (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α)) →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2
        (fun y : EuclN => ∑ ε ∈ S,
          Λgrad (I := I) (M := M) g α ε y *
            partialDerivOnEuclid (I := I) (M := M) α ε
              (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro S
    induction S using Finset.induction with
    | empty =>
        intro _
        simp only [Finset.sum_empty]
        exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_zero_fun
          (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (chartTargetEuclid_isOpen (I := I) (M := M) α)
    | insert δ S' hδ ih2 =>
        intro hf
        have hf_δ : _ := hf δ (Finset.mem_insert_self δ S')
        have hf_S' : ∀ ε ∈ S', _ := fun ε hε =>
          hf ε (Finset.mem_insert_of_mem hε)
        have hsum : _ := ih2 hf_S'
        have h_eq : (fun y : EuclN => ∑ ε ∈ insert δ S',
            Λgrad (I := I) (M := M) g α ε y *
              partialDerivOnEuclid (I := I) (M := M) α ε
                (etaTimesV (I := I) (M := M) α v.toFun) y) =
            fun y : EuclN =>
              (Λgrad (I := I) (M := M) g α δ y *
                partialDerivOnEuclid (I := I) (M := M) α δ
                  (etaTimesV (I := I) (M := M) α v.toFun) y) +
              ∑ ε ∈ S', Λgrad (I := I) (M := M) g α ε y *
                partialDerivOnEuclid (I := I) (M := M) α ε
                  (etaTimesV (I := I) (M := M) α v.toFun) y := by
          funext y; exact Finset.sum_insert hδ
        rw [h_eq]
        exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add
          (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          (chartTargetEuclid_isOpen (I := I) (M := M) α) hf_δ hsum
  have h_sum_mem :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2
        (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
          Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_sum_mem_gen Finset.univ (fun i _ => h_summand_mem i)
  have h_const2 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y => (2 : ℝ) * ∑ i : Fin (Module.finrank ℝ E),
          Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) =
      ‖(2 : ℝ)‖ₑ *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
            Λgrad (I := I) (M := M) g α i y *
              partialDerivOnEuclid (I := I) (M := M) α i
                (etaTimesV (I := I) (M := M) α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_const_smul
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) h_sum_mem (2 : ℝ)
  rw [h_const2]
  have h_triangle :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
          Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ∑ i : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α) := by
    have h_gen : ∀ (T : Finset (Fin (Module.finrank ℝ E))),
        (∀ i ∈ T, DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 2
          (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α)) →
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y : EuclN => ∑ i ∈ T,
            Λgrad (I := I) (M := M) g α i y *
              partialDerivOnEuclid (I := I) (M := M) α i
                (etaTimesV (I := I) (M := M) α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ∑ i ∈ T,
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 2
            (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
              partialDerivOnEuclid (I := I) (M := M) α i
                (etaTimesV (I := I) (M := M) α v.toFun) y)
            (chartTargetEuclid (I := I) (M := M) α) := by
      intro T
      induction T using Finset.induction with
      | empty =>
          intro _
          simp only [Finset.sum_empty]
          rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
            (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
            (chartTargetEuclid_isOpen (I := I) (M := M) α)]
      | insert γ T hγ ih =>
          intro hf_mem
          have hf_γ_mem :=
            hf_mem γ (Finset.mem_insert_self γ T)
          have hf_T_mem : ∀ ε ∈ T,
              DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
                (d := Module.finrank ℝ E) 1 2
                (fun y : EuclN => Λgrad (I := I) (M := M) g α ε y *
                  partialDerivOnEuclid (I := I) (M := M) α ε
                    (etaTimesV (I := I) (M := M) α v.toFun) y)
                (chartTargetEuclid (I := I) (M := M) α) := fun ε hε =>
            hf_mem ε (Finset.mem_insert_of_mem hε)
          have h_sumT_mem : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) 1 2
              (fun y : EuclN => ∑ ε ∈ T,
                Λgrad (I := I) (M := M) g α ε y *
                  partialDerivOnEuclid (I := I) (M := M) α ε
                    (etaTimesV (I := I) (M := M) α v.toFun) y)
              (chartTargetEuclid (I := I) (M := M) α) := by
            have h_sum_mem_T : ∀ (S : Finset (Fin (Module.finrank ℝ E))),
                (∀ ε ∈ S, DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
                  (d := Module.finrank ℝ E) 1 2
                  (fun y : EuclN => Λgrad (I := I) (M := M) g α ε y *
                    partialDerivOnEuclid (I := I) (M := M) α ε
                      (etaTimesV (I := I) (M := M) α v.toFun) y)
                  (chartTargetEuclid (I := I) (M := M) α)) →
                DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
                  (d := Module.finrank ℝ E) 1 2
                  (fun y : EuclN => ∑ ε ∈ S,
                    Λgrad (I := I) (M := M) g α ε y *
                      partialDerivOnEuclid (I := I) (M := M) α ε
                        (etaTimesV (I := I) (M := M) α v.toFun) y)
                  (chartTargetEuclid (I := I) (M := M) α) := by
              intro S
              induction S using Finset.induction with
              | empty =>
                  intro _
                  simp only [Finset.sum_empty]
                  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_zero_fun
                    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
                    (chartTargetEuclid_isOpen (I := I) (M := M) α)
              | insert δ S' hδ ih2 =>
                  intro hf
                  have hf_δ : _ := hf δ (Finset.mem_insert_self δ S')
                  have hf_S' : ∀ ε ∈ S', _ := fun ε hε =>
                    hf ε (Finset.mem_insert_of_mem hε)
                  have hsum : _ := ih2 hf_S'
                  have h_eq : (fun y : EuclN => ∑ ε ∈ insert δ S',
                      Λgrad (I := I) (M := M) g α ε y *
                        partialDerivOnEuclid (I := I) (M := M) α ε
                          (etaTimesV (I := I) (M := M) α v.toFun) y) =
                      fun y : EuclN =>
                        (Λgrad (I := I) (M := M) g α δ y *
                          partialDerivOnEuclid (I := I) (M := M) α δ
                            (etaTimesV (I := I) (M := M) α v.toFun) y) +
                        ∑ ε ∈ S', Λgrad (I := I) (M := M) g α ε y *
                          partialDerivOnEuclid (I := I) (M := M) α ε
                            (etaTimesV (I := I) (M := M) α v.toFun) y := by
                    funext y; exact Finset.sum_insert hδ
                  rw [h_eq]
                  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.add
                    (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
                    (chartTargetEuclid_isOpen (I := I) (M := M) α) hf_δ hsum
            exact h_sum_mem_T T hf_T_mem
          have h_eq : (fun y : EuclN => ∑ ε ∈ insert γ T,
              Λgrad (I := I) (M := M) g α ε y *
                partialDerivOnEuclid (I := I) (M := M) α ε
                  (etaTimesV (I := I) (M := M) α v.toFun) y) =
              fun y : EuclN =>
                (Λgrad (I := I) (M := M) g α γ y *
                  partialDerivOnEuclid (I := I) (M := M) α γ
                    (etaTimesV (I := I) (M := M) α v.toFun) y) +
                ∑ ε ∈ T, Λgrad (I := I) (M := M) g α ε y *
                  partialDerivOnEuclid (I := I) (M := M) α ε
                    (etaTimesV (I := I) (M := M) α v.toFun) y := by
            funext y; exact Finset.sum_insert hγ
          rw [h_eq, Finset.sum_insert hγ]
          have h_triangle_step :=
            DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_add_le
              (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
              (chartTargetEuclid_isOpen (I := I) (M := M) α) hf_γ_mem h_sumT_mem
          have h_ih := ih hf_T_mem
          refine h_triangle_step.trans ?_
          exact add_le_add le_rfl h_ih
    exact h_gen Finset.univ (fun i _ => h_summand_mem i)
  have h_two_norm : ‖(2 : ℝ)‖ₑ = ENNReal.ofReal 2 := by
    rw [Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h_two_norm]
  refine le_trans (mul_le_mul_of_nonneg_left h_triangle (zero_le _)) ?_
  have h_each_bound : ∀ i : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
          partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal (K i * C_partial) *
        wkpNormChart (I := I) (M := M) g 2 2 v.toFun := by
    intro i
    have h_step1 := hK_bound i (h_partial_mem i)
    have h_step2 := hC_partial_bound v i
    calc DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) 1 2
          (fun y => Λgrad (I := I) (M := M) g α i y *
            partialDerivOnEuclid (I := I) (M := M) α i
              (etaTimesV (I := I) (M := M) α v.toFun) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (K i) *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 1 2
              (partialDerivOnEuclid (I := I) (M := M) α i
                (etaTimesV (I := I) (M := M) α v.toFun))
              (chartTargetEuclid (I := I) (M := M) α) := h_step1
      _ ≤ ENNReal.ofReal (K i) *
              (ENNReal.ofReal C_partial * wkpNormChart (I := I) (M := M) g 2 2 v.toFun) :=
            mul_le_mul_of_nonneg_left h_step2 (zero_le _)
      _ = ENNReal.ofReal (K i * C_partial) *
              wkpNormChart (I := I) (M := M) g 2 2 v.toFun := by
            rw [← mul_assoc, ENNReal.ofReal_mul (hK_pos i).le]
  have h_sum_bound : ∑ i : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y : EuclN => Λgrad (I := I) (M := M) g α i y *
          partialDerivOnEuclid (I := I) (M := M) α i
            (etaTimesV (I := I) (M := M) α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ∑ i : Fin (Module.finrank ℝ E),
        ENNReal.ofReal (K i * C_partial) *
          wkpNormChart (I := I) (M := M) g 2 2 v.toFun :=
    Finset.sum_le_sum (fun i _ => h_each_bound i)
  refine le_trans (mul_le_mul_of_nonneg_left h_sum_bound (zero_le _)) ?_
  rw [← Finset.sum_mul]
  rw [show ∑ i : Fin (Module.finrank ℝ E), ENNReal.ofReal (K i * C_partial) =
      ENNReal.ofReal (∑ i : Fin (Module.finrank ℝ E), K i * C_partial) from by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _
        exact mul_nonneg (hK_pos i).le hC_partial_pos.le]
  rw [show ∑ i : Fin (Module.finrank ℝ E), K i * C_partial = sumK * C_partial from by
        rw [hsumK_def, Finset.sum_mul]]
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hCfinal_def]; linarith [mul_nonneg hsumK_nn hC_partial_pos.le]

private lemma wkpNorm_chartPushedRaw_lapPiece_le
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal C * wkpNormChart (I := I) (M := M) g 2 2
        (fun x : M => v.toFun x) := by
  classical
  obtain ⟨C_lap, hC_lap_pos, hC_lap_bound⟩ :=
    wkpNorm_chartPushedRaw_lapPiece_le_etaTimesV_aux (I := I) (M := M) g α
  obtain ⟨C_strict, hC_strict_pos, hC_strict_bound⟩ :=
    wkpNorm_chartPushedRaw_etaTimesV_le (I := I) (M := M) g α
  set Cfinal : ℝ := C_lap * C_strict with hCfinal_def
  have h_Cfinal_pos : 0 < Cfinal := mul_pos hC_lap_pos hC_strict_pos
  refine ⟨Cfinal, h_Cfinal_pos, ?_⟩
  intro v
  have h_step1 := hC_lap_bound v
  have h_step2 := hC_strict_bound v
  have h_mono : DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 1 2
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) ≤
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
      (d := Module.finrank ℝ E) 2 2
      (chartPushedRaw (I := I) (M := M) α
        (etaTimesV (I := I) (M := M) α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.EuclideanIterated.wkpNorm_mono_order
      (d := Module.finrank ℝ E) (j := 1) (k := 2) (by norm_num)
  calc DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C_lap *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) 1 2
            (chartPushedRaw (I := I) (M := M) α
              (etaTimesV (I := I) (M := M) α v.toFun))
            (chartTargetEuclid (I := I) (M := M) α) := h_step1
    _ ≤ ENNReal.ofReal C_lap *
            DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
              (d := Module.finrank ℝ E) 2 2
              (chartPushedRaw (I := I) (M := M) α
                (etaTimesV (I := I) (M := M) α v.toFun))
              (chartTargetEuclid (I := I) (M := M) α) :=
          mul_le_mul_of_nonneg_left h_mono (zero_le _)
    _ ≤ ENNReal.ofReal C_lap *
            (ENNReal.ofReal C_strict * wkpNormChart (I := I) (M := M) g 2 2 v.toFun) :=
          mul_le_mul_of_nonneg_left h_step2 (zero_le _)
    _ = ENNReal.ofReal (C_lap * C_strict) *
            wkpNormChart (I := I) (M := M) g 2 2 v.toFun := by
          rw [← mul_assoc, ENNReal.ofReal_mul hC_lap_pos.le]
    _ = ENNReal.ofReal Cfinal *
            wkpNormChart (I := I) (M := M) g 2 2 v.toFun := by
          rw [hCfinal_def]

theorem wkpNorm_smoothFChartResidual_le_wkpNormChart
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : SmoothScalar g,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidual.smoothFChartResidual
          (I := I) (M := M) g α v)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C * wkpNormChart (I := I) (M := M) g 2 2 v.toFun := by
  classical
  obtain ⟨C_grad, hC_grad_pos, hC_grad_bound⟩ :=
    wkpNorm_chartPushedRaw_gradInnerPiece_le (I := I) (M := M) g α
  obtain ⟨C_lap, hC_lap_pos, hC_lap_bound⟩ :=
    wkpNorm_chartPushedRaw_lapPiece_le (I := I) (M := M) g α
  refine ⟨C_grad + C_lap, by linarith, ?_⟩
  intro v
  have h_ae := smoothFChartResidual_ae_eq_chartPushedRaw_smoothRep
    (I := I) (M := M) g α v
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
        (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae]
  have h_ptwise : chartPushedRaw (I := I) (M := M) α
        (smoothRep (I := I) (M := M) g α v) =
      fun y => -chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y -
        chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y := by
    funext y
    exact chartPushedRaw_smoothRep_eq (I := I) (M := M) g α v y
  rw [h_ptwise]
  have hP_grad : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_w1p :=
      DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualMemW1p.memW1p_chartPushedRaw_of_contMDiff_tsupport
        (I := I) (M := M)
        (f := gradInnerPiece (I := I) (M := M) g α v.toFun) (α := α)
        (gradInnerPiece_smooth (I := I) (M := M) g α v)
        (tsupport_gradInnerPiece_subset_source (I := I) (M := M) g α v.toFun) 2
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mpr h_w1p
  have hP_lap : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (chartPushedRaw (I := I) (M := M) α
        (lapPiece (I := I) (M := M) g α v.toFun))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_w1p :=
      DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplResidualMemW1p.memW1p_chartPushedRaw_of_contMDiff_tsupport
        (I := I) (M := M)
        (f := lapPiece (I := I) (M := M) g α v.toFun) (α := α)
        (lapPiece_smooth (I := I) (M := M) g α v)
        (tsupport_lapPiece_subset_source (I := I) (M := M) g α v.toFun) 2
    exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p).mpr h_w1p
  have h_rewrite : (fun y : EuclN => -chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y -
        chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y) =
      (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y +
        ((-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y)) := by
    funext y; ring
  rw [h_rewrite]
  have hP_negA : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
        (gradInnerPiece (I := I) (M := M) g α v.toFun) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.const_smul
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) hP_grad (-1 : ℝ)
  have hP_negB : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
        (lapPiece (I := I) (M := M) g α v.toFun) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.const_smul
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) hP_lap (-1 : ℝ)
  have h_triangle :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_add_le
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (chartTargetEuclid_isOpen (I := I) (M := M) α) hP_negA hP_negB
  refine le_trans h_triangle ?_
  have h_neg_norm_grad :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_const_smul
        (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (chartTargetEuclid_isOpen (I := I) (M := M) α) hP_grad (-1 : ℝ)]
    have : ‖(-1 : ℝ)‖ₑ = 1 := by
      rw [Real.enorm_eq_ofReal_abs]
      simp
    rw [this, one_mul]
  have h_neg_norm_lap :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (fun y => (-1 : ℝ) * chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun) y)
        (chartTargetEuclid (I := I) (M := M) α) =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_const_smul
        (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        (chartTargetEuclid_isOpen (I := I) (M := M) α) hP_lap (-1 : ℝ)]
    have : ‖(-1 : ℝ)‖ₑ = 1 := by
      rw [Real.enorm_eq_ofReal_abs]
      simp
    rw [this, one_mul]
  rw [h_neg_norm_grad, h_neg_norm_lap]
  calc DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (chartPushedRaw (I := I) (M := M) α
          (gradInnerPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α) +
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) 1 2
        (chartPushedRaw (I := I) (M := M) α
          (lapPiece (I := I) (M := M) g α v.toFun))
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ ENNReal.ofReal C_grad * wkpNormChart (I := I) (M := M) g 2 2 v.toFun +
        ENNReal.ofReal C_lap * wkpNormChart (I := I) (M := M) g 2 2 v.toFun := by
            exact add_le_add (hC_grad_bound v) (hC_lap_bound v)
    _ = (ENNReal.ofReal C_grad + ENNReal.ofReal C_lap) *
        wkpNormChart (I := I) (M := M) g 2 2 v.toFun := by
            rw [add_mul]
    _ = ENNReal.ofReal (C_grad + C_lap) *
        wkpNormChart (I := I) (M := M) g 2 2 v.toFun := by
            rw [ENNReal.ofReal_add hC_grad_pos.le hC_lap_pos.le]

end HeadlineAssembly

end SmoothFChartResidualBilinearBound
end Laplacian
end Analysis
end DifferentialGeometry

end
