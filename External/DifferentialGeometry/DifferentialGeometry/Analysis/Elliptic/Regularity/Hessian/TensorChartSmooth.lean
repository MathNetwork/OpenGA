import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.SmoothCasePairingIdentification


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianTensorChartSmooth

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
open DifferentialGeometry.Analysis.Laplacian.HessianBridge
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def chartHessianVOnEuclid
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (k l : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  chartHessianTensor (I := I) g α v.toFun k l
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma chartHessianVOnEuclid_def
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (k l : Fin (Module.finrank ℝ E)) (y : EuclN) :
    chartHessianVOnEuclid (I := I) (M := M) g α v k l y =
      chartHessianTensor (I := I) g α v.toFun k l
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := rfl

noncomputable def chartPushedChristoffelCorrection
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (k l : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  ∑ m : Fin (Module.finrank ℝ E),
    chartChristoffel (I := I) g α k l m ((toEuclidean (E := E)).symm y) *
      partialDeriv (E := E) m (scalarOnE (I := I) α v.toFun)
        ((toEuclidean (E := E)).symm y)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma chartPushedChristoffelCorrection_def
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (k l : Fin (Module.finrank ℝ E)) (y : EuclN) :
    chartPushedChristoffelCorrection (I := I) (M := M) g α v k l y =
      ∑ m : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g α k l m ((toEuclidean (E := E)).symm y) *
          partialDeriv (E := E) m (scalarOnE (I := I) α v.toFun)
            ((toEuclidean (E := E)).symm y) := rfl

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartHessianVOnEuclid_eq_plain_minus_chris_on_chart_target
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (k l : Fin (Module.finrank ℝ E)) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartHessianVOnEuclid (I := I) (M := M) g α v k l y =
      chartIteratedPartialDeriv (I := I) α v.toFun k l ((toEuclidean (E := E)).symm y) -
        chartPushedChristoffelCorrection (I := I) (M := M) g α v k l y := by
  classical
  rw [chartHessianVOnEuclid_def, chartHessianTensor_def,
    chartPushedChristoffelCorrection_def]
  have hy_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target :=
    toEuclidean_symm_mem_target (I := I) hy
  have h_inv : extChartAt I α
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      (toEuclidean (E := E)).symm y :=
    (extChartAt I α).right_inv hy_target
  rw [h_inv]

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartPushedChristoffelCorrection_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (k l : Fin (Module.finrank ℝ E)) :
    ContinuousOn (chartPushedChristoffelCorrection (I := I) (M := M) g α v k l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold chartPushedChristoffelCorrection
  refine continuousOn_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun m _ => ?_)
  have h_toE_cont : Continuous (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
    (toEuclidean (E := E)).symm.continuous
  have h_int_eq_target : interior (extChartAt I α).target = (extChartAt I α).target :=
    (isOpen_extChartAt_target (I := I) α).interior_eq
  have h_chris_cont : ContinuousOn (chartChristoffel (I := I) g α k l m)
      (extChartAt I α).target := by
    rw [← h_int_eq_target]
    exact (chartChristoffel_contDiffOn_interior (I := I) g α k l m).continuousOn
  have h_smooth_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) α v.toFun)
      (extChartAt I α).target :=
    scalarOnE_contDiffOn (I := I) α v.smooth
  have h_pd_cont : ContinuousOn
      (partialDeriv (E := E) m (scalarOnE (I := I) α v.toFun))
      (extChartAt I α).target := by
    unfold partialDeriv
    rw [← h_int_eq_target]
    have h_smooth_int : ContDiffOn ℝ ∞ (scalarOnE (I := I) α v.toFun)
        (interior (extChartAt I α).target) := h_smooth_target.mono interior_subset
    have h_fder : ContDiffOn ℝ ∞
        (fderiv ℝ (scalarOnE (I := I) α v.toFun))
        (interior (extChartAt I α).target) :=
      h_smooth_int.fderiv_of_isOpen isOpen_interior
        (by rw [ENat.coe_top_add_one])
    exact (h_fder.clm_apply contDiffOn_const).continuousOn
  have h_maps : MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := fun y hy =>
    toEuclidean_symm_mem_target (I := I) hy
  have h_chris_comp : ContinuousOn
      (fun y : EuclN => chartChristoffel (I := I) g α k l m
        ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_chris_cont.comp h_toE_cont.continuousOn h_maps
  have h_pd_comp : ContinuousOn
      (fun y : EuclN => partialDeriv (E := E) m (scalarOnE (I := I) α v.toFun)
        ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_pd_cont.comp h_toE_cont.continuousOn h_maps
  exact h_chris_comp.mul h_pd_comp

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem chartHessianVOnEuclid_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (k l : Fin (Module.finrank ℝ E)) :
    ContinuousOn (chartHessianVOnEuclid (I := I) (M := M) g α v k l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hrewrite : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      chartHessianVOnEuclid (I := I) (M := M) g α v k l y =
        chartIteratedPartialDeriv (I := I) α v.toFun k l
          ((toEuclidean (E := E)).symm y) -
        chartPushedChristoffelCorrection (I := I) (M := M) g α v k l y :=
    fun y hy =>
      chartHessianVOnEuclid_eq_plain_minus_chris_on_chart_target
        (I := I) (M := M) g α v k l hy
  refine ContinuousOn.congr ?_ hrewrite
  refine ContinuousOn.sub ?_ ?_
  · have h_toE_cont : Continuous (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
      (toEuclidean (E := E)).symm.continuous
    have h_smooth_target : ContDiffOn ℝ ∞ (scalarOnE (I := I) α v.toFun)
        (extChartAt I α).target :=
      scalarOnE_contDiffOn (I := I) α v.smooth
    have h_smooth_iter : ContDiffOn ℝ ∞
        (chartIteratedPartialDeriv (I := I) α v.toFun k l)
        (extChartAt I α).target := by
      unfold chartIteratedPartialDeriv partialDeriv
      have h_fder1 : ContDiffOn ℝ ∞
          (fderiv ℝ (scalarOnE (I := I) α v.toFun))
          (extChartAt I α).target :=
        h_smooth_target.fderiv_of_isOpen (isOpen_extChartAt_target (I := I) α)
          (by rw [ENat.coe_top_add_one])
      have h_pd_j : ContDiffOn ℝ ∞
          (fun z : E => fderiv ℝ (scalarOnE (I := I) α v.toFun) z
            ((chartModelBasis E) l))
          (extChartAt I α).target :=
        h_fder1.clm_apply contDiffOn_const
      have h_fder2 : ContDiffOn ℝ ∞
          (fderiv ℝ (fun z : E => fderiv ℝ (scalarOnE (I := I) α v.toFun) z
            ((chartModelBasis E) l)))
          (extChartAt I α).target :=
        h_pd_j.fderiv_of_isOpen (isOpen_extChartAt_target (I := I) α)
          (by rw [ENat.coe_top_add_one])
      exact h_fder2.clm_apply contDiffOn_const
    have h_maps : MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y)
        (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := fun y hy =>
      toEuclidean_symm_mem_target (I := I) hy
    exact h_smooth_iter.continuousOn.comp h_toE_cont.continuousOn h_maps
  · exact chartPushedChristoffelCorrection_continuousOn (I := I) (M := M) g α v k l

noncomputable def smoothTensorPairingChart
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (y : EuclN) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          invGramOnEuclid (I := I) g α i k y *
            invGramOnEuclid (I := I) g α j l y *
            chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
            chartHessianVOnEuclid (I := I) (M := M) g α v k l y

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma smoothTensorPairingChart_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (y : EuclN) :
    smoothTensorPairingChart (I := I) (M := M) g α φ v y =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              invGramOnEuclid (I := I) g α i k y *
                invGramOnEuclid (I := I) g α j l y *
                chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y *
                chartHessianVOnEuclid (I := I) (M := M) g α v k l y := rfl

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma invGramOnEuclid_continuousOn_chartTargetEuclid
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (invGramOnEuclid (I := I) g α i j)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold invGramOnEuclid
  have h_toE_cont : Continuous (fun y : EuclN => (toEuclidean (E := E)).symm y) :=
    (toEuclidean (E := E)).symm.continuous
  have h_invGram_smooth : ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α i j)
      (extChartAt I α).target :=
    chartInvGramOnE_contDiffOn (I := I) g α i j
  have h_invGram_cont : ContinuousOn (chartInvGramOnE (I := I) g α i j)
      (extChartAt I α).target := h_invGram_smooth.continuousOn
  have h_maps : MapsTo (fun y : EuclN => (toEuclidean (E := E)).symm y)
      (chartTargetEuclid (I := I) (M := M) α) (extChartAt I α).target := fun y hy =>
    toEuclidean_symm_mem_target (I := I) hy
  have hcomp : ContinuousOn (fun y : EuclN => chartInvGramOnE (I := I) g α i j
      ((toEuclidean (E := E)).symm y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    h_invGram_cont.comp h_toE_cont.continuousOn h_maps
  refine hcomp.congr ?_
  intro y _hy
  rfl

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem smoothTensorPairingChart_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    ContinuousOn (smoothTensorPairingChart (I := I) (M := M) g α φ v)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold smoothTensorPairingChart
  refine continuousOn_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun i _ => ?_)
  refine continuousOn_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun j _ => ?_)
  refine continuousOn_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun k _ => ?_)
  refine continuousOn_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun l _ => ?_)
  have h_G_ik : ContinuousOn (invGramOnEuclid (I := I) g α i k)
      (chartTargetEuclid (I := I) (M := M) α) :=
    invGramOnEuclid_continuousOn_chartTargetEuclid (I := I) (M := M) g α i k
  have h_G_jl : ContinuousOn (invGramOnEuclid (I := I) g α j l)
      (chartTargetEuclid (I := I) (M := M) α) :=
    invGramOnEuclid_continuousOn_chartTargetEuclid (I := I) (M := M) g α j l
  have h_Hphi : ContinuousOn (chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j)
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartHessianPhiOnEuclid_continuousOn (I := I) (M := M) g α φ i j
  have h_Hv : ContinuousOn (chartHessianVOnEuclid (I := I) (M := M) g α v k l)
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartHessianVOnEuclid_continuousOn (I := I) (M := M) g α v k l
  exact (((h_G_ik.mul h_G_jl).mul h_Hphi).mul h_Hv)

noncomputable def cutoffHessianV
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (k l : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  chartCutoffα (I := I) (M := M) α y *
    chartHessianVOnEuclid (I := I) (M := M) g α v k l y

@[simp] lemma cutoffHessianV_def
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (k l : Fin (Module.finrank ℝ E)) (y : EuclN) :
    cutoffHessianV (I := I) (M := M) g α v k l y =
      chartCutoffα (I := I) (M := M) α y *
        chartHessianVOnEuclid (I := I) (M := M) g α v k l y := rfl

noncomputable def cutoffHessianPhiPub
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) : ℝ :=
  chartCutoffα (I := I) (M := M) α y *
    chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y

@[simp] lemma cutoffHessianPhiPub_def
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) (y : EuclN) :
    cutoffHessianPhiPub (I := I) (M := M) g α φ i j y =
      chartCutoffα (I := I) (M := M) α y *
        chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y := rfl

theorem cutoffHessianV_continuous
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (k l : Fin (Module.finrank ℝ E)) :
    Continuous (cutoffHessianV (I := I) (M := M) g α v k l) := by
  classical
  set η := chartCutoffα (I := I) (M := M) α with hη_def
  set Ω := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kη : Set EuclN := tsupport η with hKη_def
  have hη_cont : Continuous η :=
    (chartCutoffα_smooth (I := I) (M := M) α).continuous
  have hKη_compact : IsCompact Kη :=
    chartCutoffα_compactSupport (I := I) (M := M) α
  have hKη_sub_Ω : Kη ⊆ Ω := chartCutoffα_tsupport (I := I) (M := M) α
  have hΩ_open : IsOpen Ω :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_zero_off : ∀ y : EuclN, y ∉ Kη →
      cutoffHessianV (I := I) (M := M) g α v k l y = 0 := by
    intro y hy
    have hη_zero : chartCutoffα (I := I) (M := M) α y = 0 :=
      image_eq_zero_of_notMem_tsupport hy
    unfold cutoffHessianV
    rw [hη_zero, zero_mul]
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hyKη : y ∈ Kη
  · have hyΩ : y ∈ Ω := hKη_sub_Ω hyKη
    have hH_cont_at : ContinuousAt (chartHessianVOnEuclid (I := I) (M := M) g α v k l) y :=
      (chartHessianVOnEuclid_continuousOn (I := I) (M := M) g α v k l).continuousAt
        (hΩ_open.mem_nhds hyΩ)
    have hη_cont_at : ContinuousAt η y := hη_cont.continuousAt
    exact hη_cont_at.mul hH_cont_at
  · have h_nbd : (Kη)ᶜ ∈ 𝓝 y :=
      (isClosed_tsupport η).isOpen_compl.mem_nhds hyKη
    have h_eventually_zero :
        cutoffHessianV (I := I) (M := M) g α v k l =ᶠ[𝓝 y]
          (fun _ => (0 : ℝ)) := by
      filter_upwards [h_nbd] with z hz
      exact h_zero_off z hz
    exact (continuousAt_const (y := (0 : ℝ))).congr h_eventually_zero.symm

theorem cutoffHessianPhiPub_continuous
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) :
    Continuous (cutoffHessianPhiPub (I := I) (M := M) g α φ i j) := by
  classical
  set η := chartCutoffα (I := I) (M := M) α with hη_def
  set Ω := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kη : Set EuclN := tsupport η with hKη_def
  have hη_cont : Continuous η :=
    (chartCutoffα_smooth (I := I) (M := M) α).continuous
  have hKη_compact : IsCompact Kη :=
    chartCutoffα_compactSupport (I := I) (M := M) α
  have hKη_sub_Ω : Kη ⊆ Ω := chartCutoffα_tsupport (I := I) (M := M) α
  have hΩ_open : IsOpen Ω :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_zero_off : ∀ y : EuclN, y ∉ Kη →
      cutoffHessianPhiPub (I := I) (M := M) g α φ i j y = 0 := by
    intro y hy
    have hη_zero : chartCutoffα (I := I) (M := M) α y = 0 :=
      image_eq_zero_of_notMem_tsupport hy
    unfold cutoffHessianPhiPub
    rw [hη_zero, zero_mul]
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hyKη : y ∈ Kη
  · have hyΩ : y ∈ Ω := hKη_sub_Ω hyKη
    have hH_cont_at : ContinuousAt (chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j) y :=
      (chartHessianPhiOnEuclid_continuousOn (I := I) (M := M) g α φ i j).continuousAt
        (hΩ_open.mem_nhds hyΩ)
    have hη_cont_at : ContinuousAt η y := hη_cont.continuousAt
    exact hη_cont_at.mul hH_cont_at
  · have h_nbd : (Kη)ᶜ ∈ 𝓝 y :=
      (isClosed_tsupport η).isOpen_compl.mem_nhds hyKη
    have h_eventually_zero :
        cutoffHessianPhiPub (I := I) (M := M) g α φ i j =ᶠ[𝓝 y]
          (fun _ => (0 : ℝ)) := by
      filter_upwards [h_nbd] with z hz
      exact h_zero_off z hz
    exact (continuousAt_const (y := (0 : ℝ))).congr h_eventually_zero.symm

theorem cutoffHessianV_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (k l : Fin (Module.finrank ℝ E)) :
    HasCompactSupport (cutoffHessianV (I := I) (M := M) g α v k l) := by
  classical
  have hKη_compact : IsCompact (tsupport (chartCutoffα (I := I) (M := M) α)) :=
    chartCutoffα_compactSupport (I := I) (M := M) α
  refine HasCompactSupport.of_support_subset_isCompact hKη_compact ?_
  intro y hy
  simp only [Function.mem_support] at hy
  by_contra h_not_in
  apply hy
  have hη_zero : chartCutoffα (I := I) (M := M) α y = 0 :=
    image_eq_zero_of_notMem_tsupport h_not_in
  unfold cutoffHessianV
  rw [hη_zero, zero_mul]

theorem cutoffHessianPhiPub_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E)) :
    HasCompactSupport (cutoffHessianPhiPub (I := I) (M := M) g α φ i j) := by
  classical
  have hKη_compact : IsCompact (tsupport (chartCutoffα (I := I) (M := M) α)) :=
    chartCutoffα_compactSupport (I := I) (M := M) α
  refine HasCompactSupport.of_support_subset_isCompact hKη_compact ?_
  intro y hy
  simp only [Function.mem_support] at hy
  by_contra h_not_in
  apply hy
  have hη_zero : chartCutoffα (I := I) (M := M) α y = 0 :=
    image_eq_zero_of_notMem_tsupport h_not_in
  unfold cutoffHessianPhiPub
  rw [hη_zero, zero_mul]

theorem cutoffHessianV_bounded
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (k l : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : EuclN,
      |cutoffHessianV (I := I) (M := M) g α v k l y| ≤ C := by
  classical
  set η := chartCutoffα (I := I) (M := M) α with hη_def
  set Kη : Set EuclN := tsupport η with hKη_def
  have hKη_compact : IsCompact Kη :=
    chartCutoffα_compactSupport (I := I) (M := M) α
  have h_cont : Continuous (cutoffHessianV (I := I) (M := M) g α v k l) :=
    cutoffHessianV_continuous (I := I) (M := M) g α v k l
  have h_zero_off : ∀ y : EuclN, y ∉ Kη →
      cutoffHessianV (I := I) (M := M) g α v k l y = 0 := by
    intro y hy
    have hη_zero : chartCutoffα (I := I) (M := M) α y = 0 :=
      image_eq_zero_of_notMem_tsupport hy
    unfold cutoffHessianV
    rw [hη_zero, zero_mul]
  by_cases hKη_ne : Kη.Nonempty
  · have h_norm_cont : ContinuousOn
        (fun y : EuclN => ‖cutoffHessianV (I := I) (M := M) g α v k l y‖) Kη :=
      h_cont.continuousOn.norm
    obtain ⟨y₀, _hy₀_K, hy₀_max⟩ :=
      hKη_compact.exists_isMaxOn hKη_ne h_norm_cont
    set C := ‖cutoffHessianV (I := I) (M := M) g α v k l y₀‖ with hC_def
    have hC_nn : 0 ≤ C := norm_nonneg _
    refine ⟨C, hC_nn, ?_⟩
    intro y
    by_cases hyK : y ∈ Kη
    · have h := hy₀_max hyK
      have h_eq : |cutoffHessianV (I := I) (M := M) g α v k l y| =
          ‖cutoffHessianV (I := I) (M := M) g α v k l y‖ := rfl
      rw [h_eq]; exact h
    · rw [h_zero_off y hyK, abs_zero]; exact hC_nn
  · refine ⟨0, le_refl 0, ?_⟩
    intro y
    have hy_notK : y ∉ Kη := fun hyK => hKη_ne ⟨y, hyK⟩
    rw [h_zero_off y hy_notK, abs_zero]

noncomputable def cutoffSmoothTensorPairingChart
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (y : EuclN) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          cutoffInvGram (I := I) (M := M) g α i k y *
            cutoffInvGram (I := I) (M := M) g α j l y *
            cutoffHessianPhiPub (I := I) (M := M) g α φ i j y *
            cutoffHessianV (I := I) (M := M) g α v k l y

@[simp] lemma cutoffSmoothTensorPairingChart_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (y : EuclN) :
    cutoffSmoothTensorPairingChart (I := I) (M := M) g α φ v y =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              cutoffInvGram (I := I) (M := M) g α i k y *
                cutoffInvGram (I := I) (M := M) g α j l y *
                cutoffHessianPhiPub (I := I) (M := M) g α φ i j y *
                cutoffHessianV (I := I) (M := M) g α v k l y := rfl

theorem cutoffSmoothTensorPairingChart_continuous
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    Continuous (cutoffSmoothTensorPairingChart (I := I) (M := M) g α φ v) := by
  classical
  unfold cutoffSmoothTensorPairingChart
  refine continuous_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun i _ => ?_)
  refine continuous_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun j _ => ?_)
  refine continuous_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun k _ => ?_)
  refine continuous_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun l _ => ?_)
  have h_G_ik : Continuous (cutoffInvGram (I := I) (M := M) g α i k) :=
    cutoffInvGram_continuous (I := I) (M := M) g α i k
  have h_G_jl : Continuous (cutoffInvGram (I := I) (M := M) g α j l) :=
    cutoffInvGram_continuous (I := I) (M := M) g α j l
  have h_Hphi : Continuous (cutoffHessianPhiPub (I := I) (M := M) g α φ i j) :=
    cutoffHessianPhiPub_continuous (I := I) (M := M) g α φ i j
  have h_Hv : Continuous (cutoffHessianV (I := I) (M := M) g α v k l) :=
    cutoffHessianV_continuous (I := I) (M := M) g α v k l
  exact (((h_G_ik.mul h_G_jl).mul h_Hphi).mul h_Hv)

theorem cutoffSmoothTensorPairingChart_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    HasCompactSupport (cutoffSmoothTensorPairingChart (I := I) (M := M) g α φ v) := by
  classical
  have hKη_compact : IsCompact (tsupport (chartCutoffα (I := I) (M := M) α)) :=
    chartCutoffα_compactSupport (I := I) (M := M) α
  refine HasCompactSupport.of_support_subset_isCompact hKη_compact ?_
  intro y hy
  simp only [Function.mem_support] at hy
  by_contra h_not_in
  apply hy
  have hη_zero : chartCutoffα (I := I) (M := M) α y = 0 :=
    image_eq_zero_of_notMem_tsupport h_not_in
  unfold cutoffSmoothTensorPairingChart
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro l _
  have h_Hv_zero : cutoffHessianV (I := I) (M := M) g α v k l y = 0 := by
    unfold cutoffHessianV
    rw [hη_zero, zero_mul]
  rw [h_Hv_zero, mul_zero]

theorem cutoffSmoothTensorPairingChart_memLp_two
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    MemLp (cutoffSmoothTensorPairingChart (I := I) (M := M) g α φ v) 2
      ((volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  have h_cont : Continuous (cutoffSmoothTensorPairingChart (I := I) (M := M) g α φ v) :=
    cutoffSmoothTensorPairingChart_continuous (I := I) (M := M) g α φ v
  have h_supp : HasCompactSupport (cutoffSmoothTensorPairingChart (I := I) (M := M) g α φ v) :=
    cutoffSmoothTensorPairingChart_hasCompactSupport (I := I) (M := M) g α φ v
  exact h_cont.memLp_of_hasCompactSupport h_supp

theorem cutoffHessianV_eq_chartHessianVOnEuclid_on_kernel
    (g : SmoothRiemannianMetric I M) (α : M) (v : SmoothScalar g)
    (k l : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartImagePOUTsupport (I := I) (M := M) α) :
    cutoffHessianV (I := I) (M := M) g α v k l y =
      chartHessianVOnEuclid (I := I) (M := M) g α v k l y := by
  classical
  have hη_one : chartCutoffα (I := I) (M := M) α y = 1 :=
    chartCutoffα_eq_one_on_K (I := I) (M := M) α y hy
  unfold cutoffHessianV
  rw [hη_one, one_mul]

theorem cutoffHessianPhiPub_eq_chartHessianPhiOnEuclid_on_kernel
    (g : SmoothRiemannianMetric I M) (α : M) (φ : C^∞⟮I, M; ℝ⟯)
    (i j : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartImagePOUTsupport (I := I) (M := M) α) :
    cutoffHessianPhiPub (I := I) (M := M) g α φ i j y =
      chartHessianPhiOnEuclid (I := I) (M := M) g α φ i j y := by
  classical
  have hη_one : chartCutoffα (I := I) (M := M) α y = 1 :=
    chartCutoffα_eq_one_on_K (I := I) (M := M) α y hy
  unfold cutoffHessianPhiPub
  rw [hη_one, one_mul]

theorem cutoffSmoothTensorPairingChart_eq_on_kernel
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    {y : EuclN} (hy : y ∈ chartImagePOUTsupport (I := I) (M := M) α) :
    cutoffSmoothTensorPairingChart (I := I) (M := M) g α φ v y =
      smoothTensorPairingChart (I := I) (M := M) g α φ v y := by
  classical
  have hη_one : chartCutoffα (I := I) (M := M) α y = 1 :=
    chartCutoffα_eq_one_on_K (I := I) (M := M) α y hy
  rw [cutoffSmoothTensorPairingChart_def, smoothTensorPairingChart_def]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  unfold cutoffInvGram cutoffHessianPhiPub cutoffHessianV
  rw [hη_one]
  ring

noncomputable def smoothPairingChristoffelDiff
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (y : EuclN) : ℝ :=
  smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v y -
    smoothTensorPairingChart (I := I) (M := M) g α φ v y

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma smoothPairingChristoffelDiff_def
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (y : EuclN) :
    smoothPairingChristoffelDiff (I := I) (M := M) g α φ v y =
      smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v y -
        smoothTensorPairingChart (I := I) (M := M) g α φ v y := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem smoothEuclidHessianPairingChart_eq_tensor_plus_diff
    (g : SmoothRiemannianMetric I M) (α : M)
    (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (y : EuclN) :
    smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v y =
      smoothTensorPairingChart (I := I) (M := M) g α φ v y +
        smoothPairingChristoffelDiff (I := I) (M := M) g α φ v y := by
  rw [smoothPairingChristoffelDiff_def]
  ring

end HessianTensorChartSmooth
end Laplacian
end Analysis
end DifferentialGeometry

end
