import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.ChartAlphaWeakHessian
import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.PairingLapDom
import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.TensorChartSmooth
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.MeasurablePullback


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianTensorPairingLp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness
open DifferentialGeometry.Analysis.Laplacian.HessianLpClass
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaWeakRaw
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def chartTensorPairingLocal
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (y : EuclN) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          invGramOnEuclid (I := I) g α i k y *
            invGramOnEuclid (I := I) g α j l y *
            chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
            chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l y

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartTensorPairingLocal_def
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (y : EuclN) :
    chartTensorPairingLocal (I := I) (M := M) g α φ hu_h y =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              invGramOnEuclid (I := I) g α i k y *
                invGramOnEuclid (I := I) g α j l y *
                chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
                chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l y := rfl

private lemma chosenChartFirstWeakPartial_ae_zero_off_support
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (j : Fin (Module.finrank ℝ E)) :
    chosenChartFirstWeakPartial (I := I) (M := M) g α hu_h j
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartImagePOUTsupport (I := I) (M := M) α with hV_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hK_closed : IsClosed (chartImagePOUTsupport (I := I) (M := M) α) :=
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  have hΩ_open : IsOpen Ω :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_open : IsOpen V := hΩ_open.sdiff hK_closed
  have hV_subset : V ⊆ Ω := Set.diff_subset
  unfold chosenChartFirstWeakPartial
  have h_chart_pushed_vanishes :
      (fun y : EuclN => DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) y)
        =ᵐ[(volume : Measure EuclN).restrict V]
      (fun _ : EuclN => (0 : ℝ)) := by
    refine (ae_restrict_iff' hV_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    exact chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M) α _
      hy.1 hy.2
  have h_partial_V_ae_zero : DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
      (d := Module.finrank ℝ E) 2 j
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) V
        =ᵐ[(volume : Measure EuclN).restrict V]
      (fun _ : EuclN => (0 : ℝ)) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_ae_zero_of_ae_zero
      (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hV_open
      h_chart_pushed_vanishes j
  have h_memWkp_2 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h := DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPerChartWitness.chartH2NonSmoothPOUWitness_of_laplacianDomain
      (I := I) (M := M) g hu_h α
    exact h.memWkp_two
  have h_memW1p_Ω : DeGiorgi.MemW1p 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      Ω := h_memWkp_2.memW1p
  have h_memW1p_V : DeGiorgi.MemW1p 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
      V := by
    refine ⟨?_, ?_⟩
    · exact h_memW1p_Ω.1.mono_measure (Measure.restrict_mono_set volume hV_subset)
    · intro k
      obtain ⟨gk, hgk_memLp, hgk_weak⟩ := h_memW1p_Ω.2 k
      refine ⟨gk, ?_, ?_⟩
      · exact hgk_memLp.mono_measure (Measure.restrict_mono_set volume hV_subset)
      · exact DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_subset hgk_weak
  have h_partial_Ω : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 j
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) Ω)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem h_memW1p_Ω j
  have h_partial_Ω_on_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 j
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) Ω)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) V :=
    DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_subset h_partial_Ω
  have h_partial_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 j
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) V)
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) V :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem h_memW1p_V j
  have h_loc_Ω : LocallyIntegrable
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 j
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) Ω)
      ((volume : Measure EuclN).restrict V) := by
    have hLp := DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      h_memW1p_Ω j
    exact (hLp.mono_measure (Measure.restrict_mono_set volume hV_subset)).locallyIntegrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_loc_V : LocallyIntegrable
      (DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 j
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) V)
      ((volume : Measure EuclN).restrict V) := by
    have hLp := DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      h_memW1p_V j
    exact hLp.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_ae_eq : DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
      (d := Module.finrank ℝ E) 2 j
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) Ω
        =ᵐ[(volume : Measure EuclN).restrict V]
      DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
        (d := Module.finrank ℝ E) 2 j
        (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ)) V :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hV_open h_partial_Ω_on_V h_partial_V
      h_loc_Ω h_loc_V
  exact h_ae_eq.trans h_partial_V_ae_zero

private lemma chartChristoffelCorrectionWeak_ae_zero_off_support
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (k l : Fin (Module.finrank ℝ E)) :
    chartChristoffelCorrectionWeak (I := I) (M := M) g α hu_h k l
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  unfold chartChristoffelCorrectionWeak
  have h_per_term : ∀ m : Fin (Module.finrank ℝ E),
      (fun y : EuclN => chartChristoffel (I := I) g α k l m
          ((toEuclidean (E := E)).symm y) *
            chosenChartFirstWeakPartial (I := I) (M := M) g α hu_h m y)
        =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
    intro m
    have h_partial_ae := chosenChartFirstWeakPartial_ae_zero_off_support
      (I := I) (M := M) g α hu_h m
    filter_upwards [h_partial_ae] with y hy
    rw [hy, mul_zero]
  have h_sum_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)),
      ∀ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α k l m ((toEuclidean (E := E)).symm y) *
          chosenChartFirstWeakPartial (I := I) (M := M) g α hu_h m y = 0 := by
    rw [ae_all_iff]
    intro m
    exact h_per_term m
  filter_upwards [h_sum_ae] with y hy_all
  refine Finset.sum_eq_zero ?_
  intro m _
  exact hy_all m

private lemma chosenChartSecondWeakPartial_ae_zero_off_support
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (k l : Fin (Module.finrank ℝ E)) :
    chosenChartSecondWeakPartial (I := I) (M := M) g α hu_h k l
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) :=
  laplacianDomainHessianChart_ae_zero_off_support
    (I := I) (M := M) g α hu_h k l

private lemma chartTensorWeakHessianRaw_ae_zero_off_support
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (k l : Fin (Module.finrank ℝ E)) :
    chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ)) := by
  classical
  unfold chartTensorWeakHessianRaw
  have h_second := chosenChartSecondWeakPartial_ae_zero_off_support
    (I := I) (M := M) g α hu_h k l
  have h_chris := chartChristoffelCorrectionWeak_ae_zero_off_support
    (I := I) (M := M) g α hu_h k l
  filter_upwards [h_second, h_chris] with y h1 h2
  rw [h1, h2, sub_zero]

private lemma chartTensorWeakHessianRaw_memLp_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (k l : Fin (Module.finrank ℝ E)) :
    MemLp (chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set K : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_def
  set V : Set EuclN := Ω \ K with hV_def
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hK_sub_Ω : K ⊆ Ω := chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hV_meas : MeasurableSet V := hΩ_meas.diff hK_meas
  set H : EuclN → ℝ := chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l with hH_def
  have h_on_K : MemLp H 2
      ((volume : Measure EuclN).restrict K) :=
    chartTensorWeakHessianRaw_memLp_chartTarget_compact
      (I := I) (M := M) g α hu_h k l hK_compact hK_sub_Ω
  have h_on_V_ae_zero : H =ᵐ[(volume : Measure EuclN).restrict V]
      (fun _ : EuclN => (0 : ℝ)) :=
    chartTensorWeakHessianRaw_ae_zero_off_support
      (I := I) (M := M) g α hu_h k l
  have h_H_ae_eq_indicator : H =ᵐ[(volume : Measure EuclN).restrict Ω] K.indicator H := by
    refine (ae_restrict_iff' hΩ_meas).mpr ?_
    have h_on_V := (ae_restrict_iff' hV_meas).mp h_on_V_ae_zero
    filter_upwards [h_on_V] with y h_y_zero hy_Ω
    by_cases hy_K : y ∈ K
    · rw [Set.indicator_of_mem hy_K]
    · have hy_V : y ∈ V := ⟨hy_Ω, hy_K⟩
      rw [Set.indicator_of_notMem hy_K, h_y_zero hy_V]
  refine MemLp.ae_eq h_H_ae_eq_indicator.symm ?_
  rw [memLp_indicator_iff_restrict hK_meas]
  have h_restrict_eq : ((volume : Measure EuclN).restrict Ω).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_sub_Ω
  rw [h_restrict_eq]
  exact h_on_K

private lemma chartTensorPairingLocal_ae_eq_cutoff
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    chartTensorPairingLocal (I := I) (M := M) g α φ hu_h =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN => ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              cutoffInvGram (I := I) (M := M) g α i k y *
                cutoffInvGram (I := I) (M := M) g α j l y *
                DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
                  (I := I) (M := M) g α φ i j y *
                chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l y) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set K : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hK_def
  set V : Set EuclN := Ω \ K with hV_def
  have hΩ_meas : MeasurableSet Ω :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hV_meas : MeasurableSet V := hΩ_meas.diff hK_meas
  have h_pt_K : ∀ y ∈ K, ∀ i j k l : Fin (Module.finrank ℝ E),
      invGramOnEuclid (I := I) g α i k y *
          invGramOnEuclid (I := I) g α j l y *
          chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
          chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l y =
        cutoffInvGram (I := I) (M := M) g α i k y *
          cutoffInvGram (I := I) (M := M) g α j l y *
          DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
            (I := I) (M := M) g α φ i j y *
          chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l y := by
    intro y hy i j k l
    have hη_one : chartCutoffα (I := I) (M := M) α y = 1 :=
      chartCutoffα_eq_one_on_K (I := I) (M := M) α y hy
    unfold cutoffInvGram
      DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
    rw [hη_one]; ring
  have hae_zero_all : ∀ᵐ y ∂(volume : Measure EuclN),
      ∀ (k l : Fin (Module.finrank ℝ E)), y ∈ V →
        chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l y = 0 := by
    have h_pair_ae : ∀ (p : Fin (Module.finrank ℝ E) ×
        Fin (Module.finrank ℝ E)),
        ∀ᵐ y ∂(volume : Measure EuclN), y ∈ V →
          chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h p.1 p.2 y = 0 := by
      intro p
      have h := chartTensorWeakHessianRaw_ae_zero_off_support
        (I := I) (M := M) g α hu_h p.1 p.2
      have := (ae_restrict_iff' hV_meas).mp h
      filter_upwards [this] with y hy hyV
      exact hy hyV
    have h_all : ∀ᵐ y ∂(volume : Measure EuclN),
        ∀ (p : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
          y ∈ V →
            chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h p.1 p.2 y = 0 :=
      ae_all_iff.mpr h_pair_ae
    filter_upwards [h_all] with y hy k l hyV
    exact hy ⟨k, l⟩ hyV
  refine (ae_restrict_iff' hΩ_meas).mpr ?_
  filter_upwards [hae_zero_all] with y hy_zeros hyΩ
  by_cases hyK : y ∈ K
  · rw [chartTensorPairingLocal_def]
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    exact h_pt_K y hyK i j k l
  · have hyV : y ∈ V := ⟨hyΩ, hyK⟩
    rw [chartTensorPairingLocal_def]
    have h_LHS_zero : (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              invGramOnEuclid (I := I) g α i k y *
                invGramOnEuclid (I := I) g α j l y *
                chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
                chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l y) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i _
      refine Finset.sum_eq_zero ?_
      intro j _
      refine Finset.sum_eq_zero ?_
      intro k _
      refine Finset.sum_eq_zero ?_
      intro l _
      have hH_zero : chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l y = 0 :=
        hy_zeros k l hyV
      rw [hH_zero, mul_zero]
    have h_RHS_zero : (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              cutoffInvGram (I := I) (M := M) g α i k y *
                cutoffInvGram (I := I) (M := M) g α j l y *
                DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
                  (I := I) (M := M) g α φ i j y *
                chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l y) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i _
      refine Finset.sum_eq_zero ?_
      intro j _
      refine Finset.sum_eq_zero ?_
      intro k _
      refine Finset.sum_eq_zero ?_
      intro l _
      have hH_zero : chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l y = 0 :=
        hy_zeros k l hyV
      rw [hH_zero, mul_zero]
    rw [h_LHS_zero, h_RHS_zero]

private lemma cutoffHessianPhiPub_bounded
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : EuclN,
      |DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
        (I := I) (M := M) g α φ i j y| ≤ C := by
  classical
  set η := chartCutoffα (I := I) (M := M) α with hη_def
  set Kη : Set EuclN := tsupport η with hKη_def
  have hKη_compact : IsCompact Kη :=
    chartCutoffα_compactSupport (I := I) (M := M) α
  have h_cont : Continuous
      (DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
        (I := I) (M := M) g α φ i j) :=
    DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub_continuous
      (I := I) (M := M) g α φ i j
  have h_zero_off : ∀ y : EuclN, y ∉ Kη →
      DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
        (I := I) (M := M) g α φ i j y = 0 := by
    intro y hy
    have hη_zero : chartCutoffα (I := I) (M := M) α y = 0 :=
      image_eq_zero_of_notMem_tsupport hy
    unfold DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
    rw [hη_zero, zero_mul]
  by_cases hKη_ne : Kη.Nonempty
  · have h_norm_cont : ContinuousOn (fun y : EuclN =>
        ‖DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
          (I := I) (M := M) g α φ i j y‖) Kη :=
      h_cont.continuousOn.norm
    obtain ⟨y₀, _hy₀_K, hy₀_max⟩ :=
      hKη_compact.exists_isMaxOn hKη_ne h_norm_cont
    set C := ‖DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
      (I := I) (M := M) g α φ i j y₀‖ with hC_def
    have hC_nn : 0 ≤ C := norm_nonneg _
    refine ⟨C, hC_nn, ?_⟩
    intro y
    by_cases hyK : y ∈ Kη
    · have h := hy₀_max hyK
      have h_eq : |DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
            (I := I) (M := M) g α φ i j y| =
          ‖DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
            (I := I) (M := M) g α φ i j y‖ := rfl
      rw [h_eq]; exact h
    · rw [h_zero_off y hyK, abs_zero]; exact hC_nn
  · refine ⟨0, le_refl 0, ?_⟩
    intro y
    have hy_notK : y ∉ Kη := fun hyK => hKη_ne ⟨y, hyK⟩
    rw [h_zero_off y hy_notK, abs_zero]

private lemma cutoffHessianPhiPub_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) (μ : Measure EuclN) :
    AEStronglyMeasurable
      (DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
        (I := I) (M := M) g α φ i j) μ :=
  (DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub_continuous
    (I := I) (M := M) g α φ i j).aestronglyMeasurable

private lemma cutoffTensorSummand_memLp_two
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    (i j k l : Fin (Module.finrank ℝ E)) :
    MemLp (fun y : EuclN =>
        cutoffInvGram (I := I) (M := M) g α i k y *
          cutoffInvGram (I := I) (M := M) g α j l y *
          DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
            (I := I) (M := M) g α φ i j y *
          chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  obtain ⟨C_ik, hC_ik_nn, hC_ik_bd⟩ :=
    cutoffInvGram_bounded (I := I) (M := M) g α i k
  obtain ⟨C_jl, hC_jl_nn, hC_jl_bd⟩ :=
    cutoffInvGram_bounded (I := I) (M := M) g α j l
  obtain ⟨C_φ, hC_φ_nn, hC_φ_bd⟩ :=
    cutoffHessianPhiPub_bounded (I := I) (M := M) g α φ i j
  set Ctot := C_ik * C_jl * C_φ with hCtot_def
  have hCtot_nn : 0 ≤ Ctot := by
    rw [hCtot_def]
    exact mul_nonneg (mul_nonneg hC_ik_nn hC_jl_nn) hC_φ_nn
  have h_H_lp : MemLp (chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    chartTensorWeakHessianRaw_memLp_chartTarget (I := I) (M := M) g α hu_h k l
  set bdd_fn : EuclN → ℝ := fun y =>
    Ctot * |chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l y|
    with hbdd_def
  have h_abs_H : MemLp (fun y => |chartTensorWeakHessianRaw
      (I := I) (M := M) g α hu_h k l y|) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := h_H_lp.abs
  have hbdd_memLp : MemLp bdd_fn 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := h_abs_H.const_mul Ctot
  refine MemLp.mono hbdd_memLp ?_ ?_
  · have h_aesm_ik : AEStronglyMeasurable
        (cutoffInvGram (I := I) (M := M) g α i k)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      cutoffInvGram_aestronglyMeasurable (I := I) (M := M) g α i k _
    have h_aesm_jl : AEStronglyMeasurable
        (cutoffInvGram (I := I) (M := M) g α j l)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      cutoffInvGram_aestronglyMeasurable (I := I) (M := M) g α j l _
    have h_aesm_φ : AEStronglyMeasurable
        (DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
          (I := I) (M := M) g α φ i j)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      cutoffHessianPhiPub_aestronglyMeasurable (I := I) (M := M) g α φ i j _
    have h_aesm_H : AEStronglyMeasurable
        (chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l)
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
      h_H_lp.aestronglyMeasurable
    exact ((h_aesm_ik.mul h_aesm_jl).mul h_aesm_φ).mul h_aesm_H
  · refine Filter.Eventually.of_forall ?_
    intro y
    simp only [Real.norm_eq_abs, hbdd_def]
    set H := chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l y with hH_def
    set Gik := cutoffInvGram (I := I) (M := M) g α i k y with hGik_def
    set Gjl := cutoffInvGram (I := I) (M := M) g α j l y with hGjl_def
    set Hφ := DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
      (I := I) (M := M) g α φ i j y with hHφ_def
    have h_abs_prod : |Gik * Gjl * Hφ * H| = |Gik| * |Gjl| * |Hφ| * |H| := by
      rw [abs_mul, abs_mul, abs_mul]
    rw [h_abs_prod]
    have h_bd_ik := hC_ik_bd y
    have h_bd_jl := hC_jl_bd y
    have h_bd_φ := hC_φ_bd y
    have h_H_nn : (0 : ℝ) ≤ |H| := abs_nonneg _
    have h_step1 : |Gik| * |Gjl| ≤ C_ik * C_jl := by
      calc |Gik| * |Gjl|
          ≤ C_ik * |Gjl| := mul_le_mul_of_nonneg_right h_bd_ik (abs_nonneg _)
        _ ≤ C_ik * C_jl := mul_le_mul_of_nonneg_left h_bd_jl hC_ik_nn
    have h_step2 : |Gik| * |Gjl| * |Hφ| ≤ C_ik * C_jl * C_φ :=
      calc |Gik| * |Gjl| * |Hφ|
          ≤ (C_ik * C_jl) * |Hφ| := mul_le_mul_of_nonneg_right h_step1 (abs_nonneg _)
        _ ≤ (C_ik * C_jl) * C_φ := mul_le_mul_of_nonneg_left h_bd_φ
              (mul_nonneg hC_ik_nn hC_jl_nn)
    have h_step3 : |Gik| * |Gjl| * |Hφ| * |H| ≤ Ctot * |H| := by
      rw [hCtot_def]
      exact mul_le_mul_of_nonneg_right h_step2 h_H_nn
    have h_rhs_nn : (0 : ℝ) ≤ Ctot * |H| := mul_nonneg hCtot_nn h_H_nn
    have h_abs_rhs : abs (Ctot * |H|) = Ctot * |H| := abs_of_nonneg h_rhs_nn
    rw [h_abs_rhs]
    exact h_step3

theorem chartTensorPairingLocal_memLp_two
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (chartTensorPairingLocal (I := I) (M := M) g α φ hu_h) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_ae := chartTensorPairingLocal_ae_eq_cutoff
    (I := I) (M := M) g α φ hu_h
  have h_cutoff_memLp : MemLp (fun y : EuclN =>
        ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                cutoffInvGram (I := I) (M := M) g α i k y *
                  cutoffInvGram (I := I) (M := M) g α j l y *
                  DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth.cutoffHessianPhiPub
                    (I := I) (M := M) g α φ i j y *
                  chartTensorWeakHessianRaw (I := I) (M := M) g α hu_h k l y) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) := by
    refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun i _ => ?_)
    refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun j _ => ?_)
    refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun k _ => ?_)
    refine memLp_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l _ => ?_)
    exact cutoffTensorSummand_memLp_two (I := I) (M := M) g α φ hu_h i j k l
  exact MemLp.ae_eq h_ae.symm h_cutoff_memLp

noncomputable def chartTensorPairingLocalLp
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Lp ℝ 2 ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  (chartTensorPairingLocal_memLp_two (I := I) (M := M) g α φ hu_h).toLp _

@[simp] lemma chartTensorPairingLocalLp_coeFn
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartTensorPairingLocalLp (I := I) (M := M) g α φ hu_h :
        Lp ℝ 2 ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α))) =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartTensorPairingLocal (I := I) (M := M) g α φ hu_h :=
  MemLp.coeFn_toLp _

private noncomputable def chartTensorPairingLocalMExt
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) : ℝ :=
  chartTensorPairingLocal (I := I) (M := M) g α φ hu_h
    ((toEuclidean (E := E)) (extChartAt I α x))

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartTensorPairingLocalMExt_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) :
    chartTensorPairingLocalMExt (I := I) (M := M) g φ α hu_h x =
      chartTensorPairingLocal (I := I) (M := M) g α φ hu_h
        ((toEuclidean (E := E)) (extChartAt I α x)) := rfl

noncomputable def tensorHessPairingMChartContribution
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) : ℝ :=
  (chartAtlasPOU I M α : M → ℝ) x *
    chartTensorPairingLocalMExt (I := I) (M := M) g φ α hu_h x

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorHessPairingMChartContribution_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) :
    tensorHessPairingMChartContribution (I := I) (M := M) g φ α hu_h x =
      (chartAtlasPOU I M α : M → ℝ) x *
        chartTensorPairingLocalMExt (I := I) (M := M) g φ α hu_h x := rfl

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorHessPairingMChartContribution_zero_off_source
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    tensorHessPairingMChartContribution (I := I) (M := M) g φ α hu_h x = 0 := by
  classical
  unfold tensorHessPairingMChartContribution
  have hsub :
      tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
        (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  have hx_notsupp : x ∉ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := fun h =>
    hx (hsub h)
  have hρ_zero : (chartAtlasPOU I M α : M → ℝ) x = 0 :=
    image_eq_zero_of_notMem_tsupport hx_notsupp
  rw [hρ_zero]
  ring

omit [NeZero (Module.finrank ℝ E)] in
lemma tensorHessPairingMChartContribution_eq_on_source
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {x : M} (_hx : x ∈ (chartAt H α).source) :
    tensorHessPairingMChartContribution (I := I) (M := M) g φ α hu_h x =
      (chartAtlasPOU I M α : M → ℝ) x *
        chartTensorPairingLocal (I := I) (M := M) g α φ hu_h
          ((toEuclidean (E := E)) ((extChartAt I α) x)) := by
  unfold tensorHessPairingMChartContribution chartTensorPairingLocalMExt
  rfl

private noncomputable def chartTensorPairingLocalRep
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) : EuclN → ℝ :=
  (chartTensorPairingLocalLp (I := I) (M := M) g α φ hu_h :
    Lp ℝ 2 ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)))

private lemma chartTensorPairingLocalRep_measurable
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Measurable (chartTensorPairingLocalRep (I := I) (M := M) g α φ hu_h) :=
  (Lp.stronglyMeasurable _).measurable

private lemma chartTensorPairingLocalRep_ae_eq
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    chartTensorPairingLocalRep (I := I) (M := M) g α φ hu_h =ᵐ[
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartTensorPairingLocal (I := I) (M := M) g α φ hu_h :=
  chartTensorPairingLocalLp_coeFn (I := I) (M := M) g α φ hu_h

private lemma chartTensorPairingLocalRep_memLp_two
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (chartTensorPairingLocalRep (I := I) (M := M) g α φ hu_h) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
  Lp.memLp _

private noncomputable def tensorContribSurrogate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) : ℝ :=
  (chartAtlasPOU I M α : M → ℝ) x *
    DifferentialGeometry.Analysis.Sobolev.Chart.pullbackToManifold (I := I) α
      (chartTensorPairingLocalRep (I := I) (M := M) g α φ hu_h) x

private lemma tensorContribSurrogate_measurable
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Measurable (tensorContribSurrogate (I := I) (M := M) g φ α hu_h) := by
  classical
  refine Measurable.mul ?_ ?_
  · exact ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff.continuous).measurable
  · exact DifferentialGeometry.Analysis.Sobolev.Chart.pullbackToManifold_measurable
      (I := I) α (chartTensorPairingLocalRep_measurable (I := I) (M := M) g α φ hu_h)

private lemma tensorContribSurrogate_zero_off_source
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {x : M} (hx : x ∉ (chartAt H α).source) :
    tensorContribSurrogate (I := I) (M := M) g φ α hu_h x = 0 := by
  classical
  unfold tensorContribSurrogate
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.pullbackToManifold_apply_of_notMem
    (I := I) α _ hx]
  ring

private lemma tensorContribSurrogate_tsupport_subset
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    tsupport (tensorContribSurrogate (I := I) (M := M) g φ α hu_h) ⊆
      (chartAt H α).source := by
  classical
  have h_supp_in_pou : Function.support
      (tensorContribSurrogate (I := I) (M := M) g φ α hu_h) ⊆
        Function.support fun x : M => (chartAtlasPOU I M α : M → ℝ) x := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hρ_zero
    apply hx
    unfold tensorContribSurrogate
    rw [hρ_zero]; ring
  have h_tsupp_in_pou : tsupport
      (tensorContribSurrogate (I := I) (M := M) g φ α hu_h) ⊆
        tsupport fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
    closure_mono h_supp_in_pou
  exact h_tsupp_in_pou.trans
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α)

private lemma tensorContribSurrogate_eq_on_source
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g)
    {x : M} (hx : x ∈ (chartAt H α).source) :
    tensorContribSurrogate (I := I) (M := M) g φ α hu_h x =
      (chartAtlasPOU I M α : M → ℝ) x *
        chartTensorPairingLocalRep (I := I) (M := M) g α φ hu_h
          ((toEuclidean (E := E)) ((extChartAt I α) x)) := by
  classical
  unfold tensorContribSurrogate
  rw [DifferentialGeometry.Analysis.Sobolev.Chart.pullbackToManifold_apply_of_mem
    (I := I) α _ hx]

private lemma tensorContribSurrogate_ae_eq
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    tensorContribSurrogate (I := I) (M := M) g φ α hu_h =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      tensorHessPairingMChartContribution (I := I) (M := M) g φ α hu_h := by
  classical
  have h_ae := chartTensorPairingLocalRep_ae_eq (I := I) (M := M) g α φ hu_h
  set badSet : Set EuclN := { y : EuclN |
      chartTensorPairingLocalRep (I := I) (M := M) g α φ hu_h y ≠
      chartTensorPairingLocal (I := I) (M := M) g α φ hu_h y } with hbadSet_def
  have h_bad_null : ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)) badSet = 0 := h_ae
  obtain ⟨N, h_bad_sub_N, hN_meas, hN_null⟩ :=
    exists_measurable_superset_of_null h_bad_null
  have hN_null_inter : (volume : Measure EuclN)
      (N ∩ chartTargetEuclid (I := I) (M := M) α) = 0 := by
    rw [MeasureTheory.Measure.restrict_apply hN_meas] at hN_null
    exact hN_null
  have hN_agree : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α, y ∉ N →
      chartTensorPairingLocalRep (I := I) (M := M) g α φ hu_h y =
      chartTensorPairingLocal (I := I) (M := M) g α φ hu_h y := by
    intro y _ hy_notN
    have hy_not_bad : y ∉ badSet := fun hyb => hy_notN (h_bad_sub_N hyb)
    by_contra h_ne
    exact hy_not_bad h_ne
  have hpre_null :=
    DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom.riemannianVolumeMeasure_pullback_null
      (I := I) (M := M) g α hN_meas hN_null_inter
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ hpre_null
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  by_cases hx_src : x ∈ (chartAt H α).source
  · refine ⟨hx_src, ?_⟩
    simp only [Set.mem_setOf_eq]
    have h_y_in_target : (toEuclidean (E := E)) ((extChartAt I α) x) ∈
        chartTargetEuclid (I := I) (M := M) α := by
      refine ⟨(extChartAt I α) x, ?_, rfl⟩
      have : x ∈ (extChartAt I α).source := by
        rwa [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
          (I := I) (M := M)]
      exact (extChartAt I α).map_source this
    by_contra h_not_in_N
    have h_agree_at_y := hN_agree _ h_y_in_target h_not_in_N
    apply hx
    rw [tensorContribSurrogate_eq_on_source (I := I) (M := M) g φ α hu_h hx_src,
        tensorHessPairingMChartContribution_eq_on_source (I := I) (M := M) g φ α hu_h hx_src,
        h_agree_at_y]
  · exfalso
    apply hx
    rw [tensorContribSurrogate_zero_off_source (I := I) (M := M) g φ α hu_h hx_src,
        tensorHessPairingMChartContribution_zero_off_source (I := I) (M := M) g φ α hu_h hx_src]

private lemma chartPushedRaw_tensorContribSurrogate_le_rep
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (y : EuclN) :
    ‖DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
        (tensorContribSurrogate (I := I) (M := M) g φ α hu_h) y‖ₑ ≤
      ‖chartTensorPairingLocalRep (I := I) (M := M) g α φ hu_h y‖ₑ := by
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I) (M := M) α _ hy]
    have hy_target' : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rcases hy with ⟨w, hw_target, hwy⟩
      have h_eq : (toEuclidean (E := E)).symm y = w := by
        rw [← hwy]; exact (toEuclidean (E := E)).symm_apply_apply w
      rw [h_eq]; exact hw_target
    have hx_src :
        (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (chartAt H α).source := by
      have : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) ∈ (extChartAt I α).source :=
        (extChartAt I α).map_target hy_target'
      rwa [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
        (I := I) (M := M)] at this
    rw [tensorContribSurrogate_eq_on_source (I := I) (M := M) g φ α hu_h hx_src]
    have h_toE_extChart_x :
        (toEuclidean (E := E)) ((extChartAt I α)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) = y := by
      have h_extChart_inv : (extChartAt I α)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
            (toEuclidean (E := E)).symm y :=
        (extChartAt I α).right_inv hy_target'
      rw [h_extChart_inv]
      exact (toEuclidean (E := E)).apply_symm_apply y
    rw [h_toE_extChart_x]
    have h_nn : (0 : ℝ) ≤ (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) :=
      (chartAtlasPOU I M).nonneg α _
    have h_le : (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) ≤ 1 :=
      (chartAtlasPOU I M).le_one α _
    rw [enorm_mul]
    have h_abs_le_one : ‖(chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ ≤ 1 := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg h_nn]
      have : ENNReal.ofReal ((chartAtlasPOU I M α : M → ℝ)
          ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) ≤
            ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h_le
      rw [show ((1 : ℝ≥0∞)) = ENNReal.ofReal 1 by simp]
      exact this
    calc ‖(chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))‖ₑ *
            ‖chartTensorPairingLocalRep (I := I) (M := M) g α φ hu_h y‖ₑ
        ≤ 1 * ‖chartTensorPairingLocalRep (I := I) (M := M) g α φ hu_h y‖ₑ := by
          gcongr
      _ = ‖chartTensorPairingLocalRep (I := I) (M := M) g α φ hu_h y‖ₑ := one_mul _
  · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I) (M := M) α _ hy]
    simp

private lemma tensorContribSurrogate_memLp_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (tensorContribSurrogate (I := I) (M := M) g φ α hu_h) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have h_c_meas : Measurable (tensorContribSurrogate (I := I) (M := M) g φ α hu_h) :=
    tensorContribSurrogate_measurable (I := I) (M := M) g φ α hu_h
  have h_c_tsupp : tsupport (tensorContribSurrogate (I := I) (M := M) g φ α hu_h) ⊆
      (chartAt H α).source :=
    tensorContribSurrogate_tsupport_subset (I := I) (M := M) g φ α hu_h
  obtain ⟨C_α, hC_α_pos, hC_α_bnd⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw
      (I := I) (M := M) g α (p := 2) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) h_c_meas h_c_tsupp
  have h_chart_le : eLpNorm
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
        (tensorContribSurrogate (I := I) (M := M) g φ α hu_h)) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) ≤
    eLpNorm (chartTensorPairingLocalRep (I := I) (M := M) g α φ hu_h) 2
      ((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)) :=
    eLpNorm_mono_enorm
      (chartPushedRaw_tensorContribSurrogate_le_rep
        (I := I) (M := M) g φ α hu_h)
  have h_rep_memLp := chartTensorPairingLocalRep_memLp_two
    (I := I) (M := M) g α φ hu_h
  have h_rep_eLp_lt_top := h_rep_memLp.2
  refine ⟨h_c_meas.aestronglyMeasurable, ?_⟩
  calc eLpNorm (tensorContribSurrogate (I := I) (M := M) g φ α hu_h) 2
        (riemannianVolumeMeasure (I := I) (M := M) g)
      ≤ ENNReal.ofReal C_α *
          eLpNorm (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
            (tensorContribSurrogate (I := I) (M := M) g φ α hu_h)) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := hC_α_bnd
    _ ≤ ENNReal.ofReal C_α *
          eLpNorm (chartTensorPairingLocalRep (I := I) (M := M) g α φ hu_h) 2
            ((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)) := by gcongr
    _ < ⊤ :=
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top h_rep_eLp_lt_top

theorem tensorHessPairingMChartContribution_memLp_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (tensorHessPairingMChartContribution (I := I) (M := M) g φ α hu_h) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  have h_surr_memLp := tensorContribSurrogate_memLp_two
    (I := I) (M := M) g φ α hu_h
  have h_ae_eq := tensorContribSurrogate_ae_eq (I := I) (M := M) g φ α hu_h
  exact MemLp.ae_eq h_ae_eq h_surr_memLp

noncomputable def tensorHessPairingFunc
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) : ℝ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    tensorHessPairingMChartContribution (I := I) (M := M) g φ α hu_h x

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorHessPairingFunc_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) (x : M) :
    tensorHessPairingFunc (I := I) (M := M) g φ hu_h x =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        tensorHessPairingMChartContribution (I := I) (M := M) g φ α hu_h x := rfl

theorem tensorHessPairingFunc_memLp_two
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    MemLp (tensorHessPairingFunc (I := I) (M := M) g φ hu_h) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  unfold tensorHessPairingFunc
  refine memLp_finset_sum _ ?_
  intro α _
  exact tensorHessPairingMChartContribution_memLp_two
    (I := I) (M := M) g φ α hu_h

noncomputable def tensorHessPairingLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (u_h_bundled : ↥(laplacianDomain (I := I) (M := M) g)) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (tensorHessPairingFunc_memLp_two
    (I := I) (M := M) g φ u_h_bundled.2).toLp _

@[simp] lemma tensorHessPairingLp_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (u_h_bundled : ↥(laplacianDomain (I := I) (M := M) g)) :
    tensorHessPairingLp (I := I) (M := M) g φ u_h_bundled =
      (tensorHessPairingFunc_memLp_two
        (I := I) (M := M) g φ u_h_bundled.2).toLp _ := rfl

lemma tensorHessPairingLp_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯)
    (u_h_bundled : ↥(laplacianDomain (I := I) (M := M) g)) :
    (tensorHessPairingLp (I := I) (M := M) g φ u_h_bundled :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      tensorHessPairingFunc (I := I) (M := M) g φ u_h_bundled.2 :=
  MemLp.coeFn_toLp _

def tensorPairingSmoothLeibnizDischarge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    Prop :=
  ∀ᵐ x ∂(riemannianVolumeMeasure (I := I) (M := M) g),
    (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      (chartAtlasPOU I M α : M → ℝ) x *
        chartTensorPairingLocal (I := I) (M := M) g α φ
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
          ((toEuclidean (E := E)) (extChartAt I α x))) =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma tensorPairingSmoothLeibnizDischarge_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    tensorPairingSmoothLeibnizDischarge (I := I) (M := M) g φ v ↔
      ∀ᵐ x ∂(riemannianVolumeMeasure (I := I) (M := M) g),
        (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          (chartAtlasPOU I M α : M → ℝ) x *
            chartTensorPairingLocal (I := I) (M := M) g α φ
              (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
              ((toEuclidean (E := E)) (extChartAt I α x))) =
          hessPairingChart (I := I) g φ
            (smoothScalarToContMDiffMap (I := I) (g := g) v) x := Iff.rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHessPairingFunc_aeEq_pou_weighted_chartLocal_smoothCase
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    tensorHessPairingFunc (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
      =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          chartTensorPairingLocal (I := I) (M := M) g α φ
            (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
            ((toEuclidean (E := E)) (extChartAt I α x))) := by
  classical
  refine Filter.Eventually.of_forall ?_
  intro x
  unfold tensorHessPairingFunc
  apply Finset.sum_congr rfl
  intro α _
  by_cases hx_src : x ∈ (chartAt H α).source
  · rw [tensorHessPairingMChartContribution_eq_on_source
      (I := I) (M := M) g φ α
      (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) hx_src]
  · rw [tensorHessPairingMChartContribution_zero_off_source
      (I := I) (M := M) g φ α
      (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) hx_src]
    have h_pou_subord :
        tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
          (chartAt H α).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
    have hx_notsupp : x ∉ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := fun h => hx_src (h_pou_subord h)
    have hρ_zero : (chartAtlasPOU I M α : M → ℝ) x = 0 :=
      image_eq_zero_of_notMem_tsupport hx_notsupp
    rw [hρ_zero]; ring

theorem tensorHessPairingLp_smoothCase_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : tensorPairingSmoothLeibnizDischarge (I := I) (M := M) g φ v) :
    tensorHessPairingLp (I := I) (M := M) g φ
        ⟨smoothToH1Compl (I := I) (M := M) g v,
          smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v⟩ =
      hessPairingSmoothLp (I := I) (M := M) g φ v := by
  classical
  have h_step1 := tensorHessPairingFunc_aeEq_pou_weighted_chartLocal_smoothCase
    (I := I) (M := M) g φ v
  have h_global_ae :
      tensorHessPairingFunc (I := I) (M := M) g φ
          (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
        =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
        hessPairingChart (I := I) g φ
          (smoothScalarToContMDiffMap (I := I) (g := g) v) := by
    filter_upwards [h_step1, h_discharge] with x hx_eq1 hx_eq2
    rw [hx_eq1, hx_eq2]
  apply Lp.ext_iff.mpr
  set lhs := tensorHessPairingLp (I := I) (M := M) g φ
    ⟨smoothToH1Compl (I := I) (M := M) g v,
      smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v⟩
  set rhs := hessPairingSmoothLp (I := I) (M := M) g φ v
  have h_lhs_coe := tensorHessPairingLp_coeFn (I := I) (M := M) g φ
    ⟨smoothToH1Compl (I := I) (M := M) g v,
      smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v⟩
  have h_rhs_coe := hessPairingSmoothLp_coeFn (I := I) (M := M) g φ v
  exact (h_lhs_coe.trans h_global_ae).trans h_rhs_coe.symm

end HessianTensorPairingLp
end Laplacian
end Analysis
end DifferentialGeometry

end
