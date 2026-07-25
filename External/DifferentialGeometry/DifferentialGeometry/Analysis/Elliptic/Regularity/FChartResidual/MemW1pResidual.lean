import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplResidualChain
import DifferentialGeometry.Analysis.Elliptic.Regularity.FChartResidual.LpDecomposition
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.ChartData
import DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.CLM.Leibniz
import DifferentialGeometry.Analysis.Sobolev.Manifold.RellichManifold

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace MemW1pFChartResidual

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
open DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplFinal
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private noncomputable def preimageFun
    (g : SmoothRiemannianMetric I M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) : M → ℝ :=
  fun x =>
    ((laplacianDomain.preimage (I := I) (M := M) g
        ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h⟩ :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x

private noncomputable def preimageSmoothMulH1ComplFun
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) : M → ℝ :=
  fun x =>
    ((laplacianDomain.preimage (I := I) (M := M) g
        ⟨smoothMulH1Compl (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
          smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
            (laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h)⟩ :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) x

private noncomputable def rhoAlphaFun (α : M) : M → ℝ :=
  fun x => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x

private lemma memW1p_chartPushedRaw_rhoAlpha_mul_preimage
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
          preimageFun (I := I) (M := M) g hu_h x))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_preimage_h2 : MemWkpChart (I := I) (M := M) g 2 2
      (preimageFun (I := I) (M := M) g hu_h) := by
    unfold preimageFun
    exact (laplacianDomainPow_two_h2_plus_rhs_h2 (I := I) (M := M) g hu_h).2.1
  have h_preimage_h1 : MemWkpChart (I := I) (M := M) g 1 2
      (preimageFun (I := I) (M := M) g hu_h) := by
    intro β
    have h_β := h_preimage_h2 β
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le
      (k := 1) (k' := 2) (by norm_num : 1 ≤ 2) h_β
  have h_bridge :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memW1p_chartPushedRaw_pou_mul_of_memWkpChart
      (I := I) (M := M) g (p := 2) (u := preimageFun (I := I) (M := M) g hu_h)
      h_preimage_h1 α
  convert h_bridge using 1

private lemma memW1p_chartPushedRaw_rhoAlpha_mul_preimage_smoothMulH1Compl
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_mem : smoothMulH1Compl (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartPushedRaw (I := I) (M := M) α
        (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
          preimageSmoothMulH1ComplFun (I := I) (M := M) g α hu_h x))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_mem_dom : smoothMulH1Compl (I := I) (M := M) g
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h ∈
        laplacianDomain (I := I) (M := M) g :=
    laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 h_mem
  have h_smHC_h2 : MemWkpChart (I := I) (M := M) g 2 2
      (preimageSmoothMulH1ComplFun (I := I) (M := M) g α hu_h) := by
    have h := (laplacianDomainPow_two_h2_plus_rhs_h2
      (I := I) (M := M) g h_mem).2.1
    unfold preimageSmoothMulH1ComplFun
    convert h using 0
  have h_smHC_h1 : MemWkpChart (I := I) (M := M) g 1 2
      (preimageSmoothMulH1ComplFun (I := I) (M := M) g α hu_h) := by
    intro β
    have h_β := h_smHC_h2 β
    exact DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.le_of_le
      (k := 1) (k' := 2) (by norm_num : 1 ≤ 2) h_β
  have h_bridge :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memW1p_chartPushedRaw_pou_mul_of_memWkpChart
      (I := I) (M := M) g (p := 2)
      (u := preimageSmoothMulH1ComplFun (I := I) (M := M) g α hu_h) h_smHC_h1 α
  convert h_bridge using 1

private lemma fChartResidual_aeEq_chartPushedRaw_diff
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    fChartResidual (I := I) (M := M) g α u_h =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fun y =>
        chartPushedRaw (I := I) α
          (preimageSmoothMulH1ComplFun (I := I) (M := M) g α hu_h) y -
        chartPushedRaw (I := I) α
          (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
            preimageFun (I := I) (M := M) g hu_h x) y := by
  classical
  have hu_dom : u_h ∈ laplacianDomain (I := I) (M := M) g :=
    laplacianDomainPow_succ_subset_laplacianDomain (I := I) (M := M) g 1 hu_h
  have h_lp_id := fHLeibnizGeneralResidualCLM_eq_preimageDiff
    (I := I) (M := M) g α hu_dom
  have h_clm_eq := fHLeibnizGeneralResidualCLM_eq_fHLeibnizResidualLp
    (I := I) (M := M) g α u_h
  set ρα : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α with hρα_def
  have h_residual_eq :
      fHLeibnizResidualLp (I := I) (M := M) g α u_h =
        laplacianDomain.preimage (I := I) (M := M) g
            ⟨smoothMulH1Compl (I := I) (M := M) g ρα u_h,
              smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g ρα hu_dom⟩ -
          smoothMulLp (I := I) (M := M) g ρα
            (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩) := by
    have h_def : fHLeibnizResidualLp (I := I) (M := M) g α u_h =
        leibnizCompensatedSourceResidualCLMOfSmoothFactor (I := I) (M := M) g ρα u_h := by
      rw [h_clm_eq]; rfl
    rw [h_def]
    exact h_lp_id
  set preimage_smHC_Lp :
      Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    laplacianDomain.preimage (I := I) (M := M) g
      ⟨smoothMulH1Compl (I := I) (M := M) g ρα u_h,
        smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g ρα hu_dom⟩
    with hpreimage_smHC_def
  set preimage_Lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩
    with hpreimage_Lp_def
  set smoothMul_Lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
    smoothMulLp (I := I) (M := M) g ρα preimage_Lp
    with hsmoothMul_def
  have h_chartPushed_eq :
      chartPushedRawLpFromLp (I := I) (M := M) g α
          (fHLeibnizResidualLp (I := I) (M := M) g α u_h) =
        chartPushedRawLpFromLp (I := I) (M := M) g α
          (preimage_smHC_Lp - smoothMul_Lp) := by
    rw [h_residual_eq]
  have h_coeFn_sub :=
    DifferentialGeometry.Analysis.Laplacian.GradInnerCLMLeibniz.chartPushedRawLpFromLp_coeFn_sub
    (I := I) (M := M) g inferInstance α preimage_smHC_Lp smoothMul_Lp
  have h_coeFn_eq :
      ((chartPushedRawLpFromLp (I := I) (M := M) g α
          (fHLeibnizResidualLp (I := I) (M := M) g α u_h) :
          Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) =ᵐ[
          (chartPulledWeightedMeasure (I := I) g α).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        fun y =>
          ((chartPushedRawLpFromLp (I := I) (M := M) g α preimage_smHC_Lp :
              Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y -
          ((chartPushedRawLpFromLp (I := I) (M := M) g α smoothMul_Lp :
              Lp ℝ 2 ((chartPulledWeightedMeasure (I := I) g α).restrict
                (chartTargetEuclid (I := I) (M := M) α))) : EuclN → ℝ) y := by
    rw [h_chartPushed_eq]
    exact h_coeFn_sub
  have h_preimage_smHC_aeEq :=
    chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α preimage_smHC_Lp
  have h_smoothMul_aeEq :
      ((smoothMul_Lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x : M => (ρα : M → ℝ) x * ((preimage_Lp : Lp ℝ 2 _) : M → ℝ) x :=
    smoothMulLp_apply_coeFn (I := I) (M := M) g ρα preimage_Lp
  have h_smoothMul_meas : Measurable
      ((smoothMul_Lp : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  have h_prod_meas : Measurable
      (fun x : M => (ρα : M → ℝ) x * ((preimage_Lp : Lp ℝ 2 _) : M → ℝ) x) :=
    (ρα.contMDiff.continuous).measurable.mul (Lp.stronglyMeasurable _).measurable
  have h_chartPushedRaw_smoothMul_aeEq :=
    chartPushedRaw_aeEq_of_aeEq (I := I) (M := M) g α
      h_smoothMul_meas h_prod_meas h_smoothMul_aeEq
  have h_smoothMul_coeFn_aeEq :=
    chartPushedRawLpFromLp_coeFn (I := I) (M := M) g α smoothMul_Lp
  unfold fChartResidual
  filter_upwards [h_coeFn_eq, h_preimage_smHC_aeEq, h_smoothMul_coeFn_aeEq,
    h_chartPushedRaw_smoothMul_aeEq] with y h_lhs h_pre_smHC h_smMul_coeFn h_smMul_aeEq
  rw [h_lhs, h_pre_smHC, h_smMul_coeFn, h_smMul_aeEq]
  rfl

theorem fChartResidual_memW1p_of_iteratedClosure
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_mem : smoothMulH1Compl (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h ∈
      laplacianDomainPow (I := I) (M := M) g 2)
    (h_support : preimageSmoothMulH1ComplFun (I := I) (M := M) g α hu_h =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      fun x => rhoAlphaFun (I := I) (M := M) α x *
        preimageSmoothMulH1ComplFun (I := I) (M := M) g α hu_h x) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fChartResidual (I := I) (M := M) g α u_h)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_preimage_meas : Measurable
      (preimageSmoothMulH1ComplFun (I := I) (M := M) g α hu_h) := by
    unfold preimageSmoothMulH1ComplFun
    exact (Lp.stronglyMeasurable _).measurable
  have h_prod_meas : Measurable
      (fun x => rhoAlphaFun (I := I) (M := M) α x *
        preimageSmoothMulH1ComplFun (I := I) (M := M) g α hu_h x) := by
    refine Measurable.mul ?_ h_preimage_meas
    exact ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous).measurable
  have h_chartPushed_aeEq :=
    chartPushedRaw_aeEq_of_aeEq (I := I) (M := M) g α
      h_preimage_meas h_prod_meas h_support
  have h_decomp_weighted := fChartResidual_aeEq_chartPushedRaw_diff
    (I := I) (M := M) g α hu_h
  have h_residual_rewritten :
      fChartResidual (I := I) (M := M) g α u_h =ᵐ[
        (chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fun y =>
        chartPushedRaw (I := I) α
          (fun x => rhoAlphaFun (I := I) (M := M) α x *
            preimageSmoothMulH1ComplFun (I := I) (M := M) g α hu_h x) y -
        chartPushedRaw (I := I) α
          (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
            preimageFun (I := I) (M := M) g hu_h x) y := by
    filter_upwards [h_decomp_weighted, h_chartPushed_aeEq] with y hy hyEq
    rw [hy, hyEq]
  have h_vol_abs : (volume : Measure EuclN).restrict
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
  have h_residual_rewritten_vol :
      fChartResidual (I := I) (M := M) g α u_h =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      fun y =>
        chartPushedRaw (I := I) α
          (fun x => rhoAlphaFun (I := I) (M := M) α x *
            preimageSmoothMulH1ComplFun (I := I) (M := M) g α hu_h x) y -
        chartPushedRaw (I := I) α
          (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
            preimageFun (I := I) (M := M) g hu_h x) y :=
    h_vol_abs.ae_le h_residual_rewritten
  have h_piece1 := memW1p_chartPushedRaw_rhoAlpha_mul_preimage_smoothMulH1Compl
    (I := I) (M := M) g α hu_h h_mem
  have h_piece2 := memW1p_chartPushedRaw_rhoAlpha_mul_preimage
    (I := I) (M := M) g α hu_h
  have h_piece2_neg :
      DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
        (fun y => (-1 : ℝ) * chartPushedRaw (I := I) α
          (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
            preimageFun (I := I) (M := M) g hu_h x) y)
        (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p.const_smul
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_piece2 (-1 : ℝ)
  have h_diff : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fun y =>
        chartPushedRaw (I := I) α
          (fun x => rhoAlphaFun (I := I) (M := M) α x *
            preimageSmoothMulH1ComplFun (I := I) (M := M) g α hu_h x) y -
        chartPushedRaw (I := I) α
          (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
            preimageFun (I := I) (M := M) g hu_h x) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_add := DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p.add
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_piece1 h_piece2_neg
    have h_eq : (fun y =>
        chartPushedRaw (I := I) α
          (fun x => rhoAlphaFun (I := I) (M := M) α x *
            preimageSmoothMulH1ComplFun (I := I) (M := M) g α hu_h x) y +
        (-1 : ℝ) * chartPushedRaw (I := I) α
          (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
            preimageFun (I := I) (M := M) g hu_h x) y) =
      (fun y =>
        chartPushedRaw (I := I) α
          (fun x => rhoAlphaFun (I := I) (M := M) α x *
            preimageSmoothMulH1ComplFun (I := I) (M := M) g α hu_h x) y -
        chartPushedRaw (I := I) α
          (fun x : M => rhoAlphaFun (I := I) (M := M) α x *
            preimageFun (I := I) (M := M) g hu_h x) y) := by
      funext y; ring
    rw [h_eq] at h_add
    exact h_add
  have hΩ : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
    (d := Module.finrank ℝ E) (p := 2) hΩ h_residual_rewritten_vol.symm).mp h_diff

end MemW1pFChartResidual
end Laplacian
end Analysis
end DifferentialGeometry

end
