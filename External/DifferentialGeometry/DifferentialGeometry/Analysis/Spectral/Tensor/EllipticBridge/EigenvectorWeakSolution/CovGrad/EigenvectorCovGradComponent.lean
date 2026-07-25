import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.EigenvectorCovGradPouChartComponent
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.EnergyBound.EigenvectorChartWeightedMemLp
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.PouComponentBound.CutoffChartComponentMemWkp
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Bootstrap.BootstrapSource


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix ENNReal NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma memWkp_of_hasWeakPartialDeriv
    {K : ℕ} {Ω : Set EuclN} (hΩ : IsOpen Ω)
    {k : Fin (Module.finrank ℝ E)} {gfun u : EuclN → ℝ}
    (hg_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k gfun u Ω)
    (hg_loc : LocallyIntegrable gfun ((volume : Measure EuclN).restrict Ω))
    (hu : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 u Ω) :
    MemWkp (d := Module.finrank ℝ E) K 2 gfun Ω := by
  classical
  have hu_W1 : DeGiorgi.MemW1p 2 u Ω := hu.memW1p
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω) u Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem (d := Module.finrank ℝ E) hu_W1 k
  have h_chosen_loc : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω)
      ((volume : Measure EuclN).restrict Ω) :=
    (chosenWeakPartial'_memLp_of_mem (d := Module.finrank ℝ E) hu_W1 k).locallyIntegrable
      (by norm_num)
  have h_ae : gfun =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq (d := Module.finrank ℝ E) hΩ
      hg_weak h_chosen_weak hg_loc h_chosen_loc
  have h_chosen_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω) Ω :=
    hu.chosenWeakPartial_mem k
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ h_ae).mpr h_chosen_memWkp

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma memWkp_coef_mul_factor
    (β : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) β))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) β))
    (hfactor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) β),
      y ∉ chartPouKernel (I := I) (M := M) β → factor y = 0) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  set Kβ : Set EuclN := chartPouKernel (I := I) (M := M) β with hKβ_def
  have hKβ_compact : IsCompact Kβ := chartPouKernel_isCompact (I := I) (M := M) β
  have hKβ_in_Ω : Kβ ⊆ Ω :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) β
  obtain ⟨δ, χ, hδ_pos, hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hKβ_compact hΩ_open hKβ_in_Ω
  have hχ_coef_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => χ y * coef y) := by
    have h_open_compl : IsOpen ((tsupport χ)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport χ
    · have hy_chart : y ∈ Ω := hχ_tsupp hy_supp
      exact hχ_smooth.contDiffAt.mul
        ((hcoef_chart y hy_chart).contDiffAt (hΩ_open.mem_nhds hy_chart))
    · have h_eq_zero : (fun y => χ y * coef y)
          =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hχ_coef_cs : HasCompactSupport (fun y => χ y * coef y) :=
    HasCompactSupport.mul_right hχ_cs
  obtain ⟨C, _hC_nn, hC_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hχ_coef_smooth hχ_coef_cs K
  have h_prod_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (χ y * coef y) * factor y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hχ_coef_smooth
      (fun j _hj y _hy => hC_bd y j _hj) hfactor_memWkp
  set Cδ : Set EuclN := Metric.cthickening δ Kβ with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kβ → factor y = 0 := by
    have h := hfactor_ae_zero
    rw [chartL2Measure] at h
    exact h
  have h_eq_on_inter : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict (Ω ∩ Cδ)]
      (fun y => coef y * factor y) := by
    refine (ae_restrict_iff' (hΩ_meas.inter hCδ_meas)).mpr ?_
    refine Filter.Eventually.of_forall fun y hy => ?_
    have hχy : χ y = 1 := hχ_one y hy.2
    change (χ y * coef y) * factor y = coef y * factor y
    rw [hχy]; ring
  have hKβ_in_Cδ : Kβ ⊆ Cδ := Metric.self_subset_cthickening _
  have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
      (fun y => coef y * factor y) := by
    have h_diff_in_Ω : (volume : Measure EuclN).restrict (Ω \ Cδ) ≤
        (volume : Measure EuclN).restrict Ω :=
      Measure.restrict_mono Set.diff_subset le_rfl
    have h_factor_diff : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
        factor y = 0 := by
      have h_lift : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          y ∉ Kβ → factor y = 0 :=
        (Measure.absolutelyContinuous_of_le h_diff_in_Ω).ae_le hfactor_ae_zero'
      have h_off : ∀ᵐ _y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          _y ∈ Ω \ Cδ := ae_restrict_mem (hΩ_meas.diff hCδ_meas)
      filter_upwards [h_lift, h_off] with y hy hy_mem
      exact hy (fun hyK => hy_mem.2 (hKβ_in_Cδ hyK))
    filter_upwards [h_factor_diff] with y hy
    show (χ y * coef y) * factor y = coef y * factor y
    rw [hy]; ring
  have h_diff_meas : MeasurableSet (Ω \ Cδ) := hΩ_meas.diff hCδ_meas
  have h_cover : Ω = (Ω ∩ Cδ) ∪ (Ω \ Cδ) := by
    ext y; constructor
    · intro hy
      by_cases h : y ∈ Cδ
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
  have h_disj : Disjoint (Ω ∩ Cδ) (Ω \ Cδ) :=
    Set.disjoint_left.mpr fun y hy hy' => hy'.2 hy.2
  have h_ae_eq : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    have hΩ_restrict_eq : (volume : Measure EuclN).restrict Ω =
        (volume : Measure EuclN).restrict ((Ω ∩ Cδ) ∪ (Ω \ Cδ)) := by
      rw [← h_cover]
    rw [hΩ_restrict_eq, Measure.restrict_union h_disj h_diff_meas]
    exact (ae_add_measure_iff).mpr ⟨h_eq_on_inter, h_eq_on_diff⟩
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_eq).mp h_prod_memWkp

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma eigenvectorVec_pou_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (h_pou_phi : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) N 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_res : MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    h_pou_phi β Q
  have h_chart_eq := eigenvector_chartComponent_eq (I := I) (M := M)
    g r s i β Q
  have h_ae : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i) β Q :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) β Q)
    have h_smul' : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
        (fun y => (i.fst.val)⁻¹ •
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
      rw [h_chart_eq]
      exact h_smul
    have h_smul'' : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[(volume : Measure EuclN).restrict Ω]
        (fun y => (i.fst.val)⁻¹ •
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y) := h_smul'
    filter_upwards [h_smul''] with y hy
    rw [hy, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma eigenvectorChartWeakPartial_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)
    (h_pou_phi : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s i β P k)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have hu : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    eigenvectorVec_pou_memWkp (I := I) (M := M) g r s i (K + 1)
      h_pou_phi β P
  have hg_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s i β P k)
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartWeakPartial_hasWeakPartialDeriv (I := I) (M := M)
      g r s i β P k
  have hg_loc : LocallyIntegrable
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s i β P k)
      ((volume : Measure EuclN).restrict Ω) := by
    have h_memLp : MemLp (eigenvectorChartWeakPartial (I := I)
        (M := M) g r s i β P k) 2
        ((volume : Measure EuclN).restrict Ω) := by
      rw [eigenvectorChartWeakPartial]
      exact Lp.memLp _
    exact h_memLp.locallyIntegrable (by norm_num)
  exact memWkp_of_hasWeakPartialDeriv (K := K) hΩ_open hg_weak hg_loc hu

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma covGradPouLeibnizCrossLimit_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)
    (h_pou_phi : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (covGradPouLeibnizCrossLimit (I := I) (M := M) g r s i β P k)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have hpou_supp : tsupport
      ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H β).source :=
    chartAtlasPOU_isSubordinate I M β
  have hpou_pushed_smooth : ContDiff ℝ ∞
      (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_contDiff
      (I := I) (M := M)
      (chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯).contMDiff hpou_supp
  have hpou_pushed_cs : HasCompactSupport
      (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
    DifferentialGeometry.Analysis.Laplacian.SmoothFChartResidualBilinearBound.chartPushedRaw_smooth_hasCompactSupport_local
      (I := I) (M := M) hpou_supp
  have hmult_smooth : ContDiff ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))) :=
    euclidPartial_contDiff (E := E) hpou_pushed_smooth k
  have hmult_smooth' : ContDiff ℝ (⊤ : ℕ∞)
      (euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))) :=
    hmult_smooth
  have hmult_cs : HasCompactSupport
      (euclidPartial (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))) := by
    apply HasCompactSupport.of_support_subset_isCompact hpou_pushed_cs
    intro y hy
    by_contra hy_off
    exact hy (by
      have h := euclidPartial_def (E := E) k
        (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y
      have hopen : IsOpen ((tsupport
          (chartPushedRaw I β ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)))ᶜ) :=
        (isClosed_tsupport _).isOpen_compl
      have hevt : (chartPushedRaw I β
            ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ))
          =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) :=
        Filter.eventually_of_mem (hopen.mem_nhds hy_off)
          (fun z hz => image_eq_zero_of_notMem_tsupport hz)
      rw [h, hevt.fderiv_eq]
      simp)
  obtain ⟨C, _hC_nn, hC_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hmult_smooth' hmult_cs K
  have hcutoff_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) β P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
      β P K
      (fun β' Q' => eigenvectorVec_pou_memWkp (I := I) (M := M)
        g r s i K
        (fun β'' Q'' => (h_pou_phi β'' Q'').le_of_le (Nat.le_succ K)) β' Q')
  have h_prod : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        euclidPartial (E := E) k
            (chartPushedRaw I β
              ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
    MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hmult_smooth'
      (fun j _hj y _hy => hC_bd y j _hj) hcutoff_memWkp
  change MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        euclidPartial (E := E) k
            (chartPushedRaw I β
              ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y *
          ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
  exact h_prod

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma covGradChristoffelLimit_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)
    (h_pou_phi : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (covGradChristoffelLimit (I := I) (M := M) g r s i β P k)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_summand : ∀ p : TensorCompIdx (E := E) r s,
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          Set.indicator (chartPouKernel (I := I) (M := M) β)
              (covDerivLowerOrderCoeff (I := I) (M := M)
                g r s β k P.1 p.1 P.2 p.2) y *
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β p :
              EuclN → ℝ) y) Ω := by
    intro p
    have hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β p :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω :=
      eigenvectorVec_pou_memWkp (I := I) (M := M)
        g r s i K
        (fun β' Q' => (h_pou_phi β' Q').le_of_le (Nat.le_succ K)) β p
    have hfactor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) β),
        y ∉ chartPouKernel (I := I) (M := M) β →
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β p :
            EuclN → ℝ) y = 0 :=
      tensorL2ChartComponent_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) β p
    have h_no_indicator : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y =>
          covDerivLowerOrderCoeff (I := I) (M := M)
              g r s β k P.1 p.1 P.2 p.2 y *
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β p :
              EuclN → ℝ) y) Ω :=
      memWkp_coef_mul_factor (I := I) (M := M) β K
        (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
          g r s β k P.1 p.1 P.2 p.2)
        hfactor_memWkp hfactor_ae_zero
    have h_ae : (fun y =>
          covDerivLowerOrderCoeff (I := I) (M := M)
              g r s β k P.1 p.1 P.2 p.2 y *
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β p :
              EuclN → ℝ) y)
        =ᵐ[(volume : Measure EuclN).restrict Ω]
        (fun y =>
          Set.indicator (chartPouKernel (I := I) (M := M) β)
              (covDerivLowerOrderCoeff (I := I) (M := M)
                g r s β k P.1 p.1 P.2 p.2) y *
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β p :
              EuclN → ℝ) y) := by
      have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
          y ∉ chartPouKernel (I := I) (M := M) β →
            (tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M)
                  g r s) i) β p :
              EuclN → ℝ) y = 0 := hfactor_ae_zero
      filter_upwards [hfactor_ae_zero'] with y hy
      by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) β
      · rw [Set.indicator_of_mem hyK]
      · rw [Set.indicator_of_notMem hyK, zero_mul, hy hyK, mul_zero]
    exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mp h_no_indicator
  have h_sum : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ p : TensorCompIdx (E := E) r s,
        Set.indicator (chartPouKernel (I := I) (M := M) β)
            (covDerivLowerOrderCoeff (I := I) (M := M)
              g r s β k P.1 p.1 P.2 p.2) y *
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β p :
            EuclN → ℝ) y) Ω := by
    classical
    induction (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        using Finset.induction with
    | empty =>
        simpa using MemWkp_zero_fun (d := Module.finrank ℝ E)
          (k := K) (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
    | insert a t ha ih =>
        have h_eq : (fun y => ∑ p ∈ insert a t,
              Set.indicator (chartPouKernel (I := I) (M := M) β)
                  (covDerivLowerOrderCoeff (I := I) (M := M)
                    g r s β k P.1 p.1 P.2 p.2) y *
                (tensorL2ChartComponent (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M)
                      g r s) i)
                  β p : EuclN → ℝ) y) =
            (fun y =>
              (Set.indicator (chartPouKernel (I := I) (M := M) β)
                  (covDerivLowerOrderCoeff (I := I) (M := M)
                    g r s β k P.1 a.1 P.2 a.2) y *
                (tensorL2ChartComponent (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator (I := I) (M := M)
                      g r s) i)
                  β a : EuclN → ℝ) y) +
              ∑ p ∈ t,
                Set.indicator (chartPouKernel (I := I) (M := M) β)
                    (covDerivLowerOrderCoeff (I := I) (M := M)
                      g r s β k P.1 p.1 P.2 p.2) y *
                  (tensorL2ChartComponent (I := I) (M := M) g r s
                    (tensorResolventEigenbasisVec (I := I) (M := M)
                      (tensorResolventL2_isCompactOperator (I := I)
                        (M := M) g r s) i)
                    β p : EuclN → ℝ) y) := by
          funext y
          rw [Finset.sum_insert ha]
        rw [h_eq]
        exact MemWkp.add (d := Module.finrank ℝ E)
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open (h_summand a) ih
  change MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ p : TensorCompIdx (E := E) r s,
        Set.indicator (chartPouKernel (I := I) (M := M) β)
            (covDerivLowerOrderCoeff (I := I) (M := M)
              g r s β k P.1 p.1 P.2 p.2) y *
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) β p :
            EuclN → ℝ) y) Ω
  exact h_sum

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorCovGrad_pou_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (K : ℕ)
    (h_pou_phi : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (Q' : TensorCompIdx (E := E) r (s + 1)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i)) β Q' :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  set P : TensorCompIdx (E := E) r s := (Q'.1, Matrix.vecTail Q'.2) with hP_def
  have h1 : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i β P (Q'.2 0)) Ω :=
    eigenvectorChartWeakPartial_memWkp (I := I) (M := M)
      g r s i K h_pou_phi β P (Q'.2 0)
  have h2 : MemWkp (d := Module.finrank ℝ E) K 2
      (covGradPouLeibnizCrossLimit (I := I) (M := M)
        g r s i β P (Q'.2 0)) Ω :=
    covGradPouLeibnizCrossLimit_memWkp (I := I) (M := M)
      g r s i K h_pou_phi β P (Q'.2 0)
  have h3 : MemWkp (d := Module.finrank ℝ E) K 2
      (covGradChristoffelLimit (I := I) (M := M)
        g r s i β P (Q'.2 0)) Ω :=
    covGradChristoffelLimit_memWkp (I := I) (M := M)
      g r s i K h_pou_phi β P (Q'.2 0)
  have h_sum : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y =>
        eigenvectorChartWeakPartial (I := I) (M := M)
            g r s i β P (Q'.2 0) y
          - covGradPouLeibnizCrossLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y
          + covGradChristoffelLimit (I := I) (M := M)
              g r s i β P (Q'.2 0) y) Ω :=
    MemWkp.add (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open
      (MemWkp.sub (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h1 h2) h3
  have h_ae := eigenvectorCovGrad_pou_chartComponent_ae_eq
    (I := I) (M := M) g r s i β Q'
  have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
    (tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
      (tensorCovGradL2Compl (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s i)) β Q')
  have h_scaled : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i)) β Q' :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω := by
    refine (MemWkp_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open ?_).mpr h_sum
    have h_combined : (fun y => (i.fst.val)⁻¹ *
          ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
            (tensorCovGradL2Compl (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q' : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
        (fun y =>
          eigenvectorChartWeakPartial (I := I) (M := M)
              g r s i β P (Q'.2 0) y
            - covGradPouLeibnizCrossLimit (I := I) (M := M)
                g r s i β P (Q'.2 0) y
            + covGradChristoffelLimit (I := I) (M := M)
                g r s i β P (Q'.2 0) y) := by
      filter_upwards [h_smul, h_ae] with y hy_smul hy_ae
      rw [← hy_ae, hy_smul, Pi.smul_apply, smul_eq_mul]
    exact h_combined
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  have h_rescaled : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => i.fst.val * ((i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i)) β Q' :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)) Ω :=
    MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_scaled i.fst.val
  have h_final_eq : (fun y => i.fst.val * ((i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i)) β Q' :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)) =
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r (s + 1)
          (tensorCovGradL2Compl (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s i)) β Q' :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
    funext y
    rw [mul_inv_cancel_left₀ hμ_ne]
  rw [h_final_eq] at h_rescaled
  exact h_rescaled

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
