import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.EigenvectorSmoothChartComponentSupport
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.EigenvectorSmoothChartComponentTerm
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.ChartTransition.ChartTransitionTransportCLM
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.QuasiMeasurePreserving


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid

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

private lemma ae_eq_of_ae_eq_restrict_of_eqOn_compl
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f h : X → ℝ} {s : Set X} (hs : MeasurableSet s)
    (h_restrict : f =ᵐ[μ.restrict s] h)
    (h_compl : ∀ x, x ∉ s → f x = h x) :
    f =ᵐ[μ] h := by
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  have h_diff_subset : {x | ¬ f x = h x} ⊆ s := by
    intro x hx
    by_contra hxs
    exact hx (h_compl x hxs)
  have h_inter : {x | ¬ f x = h x} = {x | ¬ f x = h x} ∩ s :=
    (Set.inter_eq_left.mpr h_diff_subset).symm
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h_restrict
  rw [MeasureTheory.Measure.restrict_apply₀'] at h_restrict
  · rwa [h_inter]
  · exact hs.nullMeasurableSet

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
    (β γ : M) {y : EuclN}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) β) :
    y ∈ chartOverlapEuclid (I := I) (M := M) β γ ↔
      (extChartAt I β).symm ((toEuclidean (E := E)).symm y) ∈
        (chartAt H γ).source := by
  classical
  set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y) with hz_def
  have hz_srcβ : z ∈ (chartAt H β).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy
  have hsymm_target : (toEuclidean (E := E)).symm y ∈ (extChartAt I β).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hy_eq : (toEuclidean (E := E)) (extChartAt I β z) = y := by
    rw [hz_def, (extChartAt I β).right_inv hsymm_target]
    exact (toEuclidean (E := E)).apply_symm_apply y
  constructor
  · rintro ⟨w, ⟨x, hx_in, hxw⟩, hwy⟩
    have hx_eq_z : x = z := by
      have hx_srcβ : x ∈ (extChartAt I β).source := by
        rw [extChartAt_source (I := I)]; exact hx_in.1
      rw [hz_def, ← hwy, ← hxw, (toEuclidean (E := E)).symm_apply_apply,
        (extChartAt I β).left_inv hx_srcβ]
    rw [hx_eq_z] at hx_in
    exact hx_in.2
  · intro hz_srcγ
    exact ⟨extChartAt I β z, ⟨z, ⟨hz_srcβ, hz_srcγ⟩, rfl⟩, hy_eq⟩

private def chartKernelCutoffPushed (γ : M) : EuclN → ℝ :=
  chartPushedRaw (I := I) (M := M) γ
    (fun x => ((chartKernelCutoff (I := I) (M := M) γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartKernelCutoffPushed_eq_one_on_chartPouKernel
    (γ : M) {y : EuclN}
    (hy : y ∈ chartPouKernel (I := I) (M := M) γ) :
    chartKernelCutoffPushed (I := I) (M := M) γ y = 1 := by
  classical
  rw [chartPouKernel] at hy
  obtain ⟨v, ⟨w, hw_supp, hwv⟩, hvy⟩ := hy
  have hw_srcγ : w ∈ (chartAt H γ).source :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) γ hw_supp
  have hw_extsrc : w ∈ (extChartAt I γ).source := by
    rw [extChartAt_source (I := I)]; exact hw_srcγ
  have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) γ :=
    chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) γ
      ⟨v, ⟨w, hw_supp, hwv⟩, hvy⟩
  have hsymm : (extChartAt I γ).symm ((toEuclidean (E := E)).symm y) = w := by
    rw [← hvy, ← hwv, (toEuclidean (E := E)).symm_apply_apply,
      (extChartAt I γ).left_inv hw_extsrc]
  unfold chartKernelCutoffPushed
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) γ _ hy_target, hsymm]
  exact chartKernelCutoff_eqOn_one (I := I) (M := M) γ hw_supp

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma chartKernelCutoffPushed_toEuclidean_extChartAt
    (γ : M) {z : M} (hz : z ∈ (chartAt H γ).source) :
    chartKernelCutoffPushed (I := I) (M := M) γ
        ((toEuclidean (E := E)) (extChartAt I γ z)) =
      ((chartKernelCutoff (I := I) (M := M) γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
  unfold chartKernelCutoffPushed
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) γ _
      (toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) γ hz),
    symm_toEuclidean_symm_toEuclidean_extChartAt (I := I) (M := M) γ hz]

omit [CompleteSpace E] in
private lemma eigenvectorChartComponentFun_ae_eq_chartKernelCutoffPushed_mul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (γ : M) (Q : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun (I := I) (M := M) g r s i γ Q
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) γ)]
      (fun y => chartKernelCutoffPushed (I := I) (M := M) γ y *
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s i γ Q y) := by
  classical
  have hK_meas : MeasurableSet (chartPouKernel (I := I) (M := M) γ) :=
    chartPouKernel_measurableSet (I := I) (M := M) γ
  have h_on_K : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) γ)),
      y ∈ chartPouKernel (I := I) (M := M) γ →
        eigenvectorChartComponentFun (I := I) (M := M) g r s i γ Q y =
          chartKernelCutoffPushed (I := I) (M := M) γ y *
            eigenvectorChartComponentFun (I := I) (M := M)
              g r s i γ Q y := by
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [chartKernelCutoffPushed_eq_one_on_chartPouKernel (I := I) (M := M) γ hy,
      one_mul]
  have h_off_raw :=
    eigenvectorChartComponentFun_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s i γ Q
  have h_off_restrict :
      eigenvectorChartComponentFun (I := I) (M := M) g r s i γ Q
        =ᵐ[((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) γ)).restrict
            (chartPouKernel (I := I) (M := M) γ)ᶜ]
        (fun _ : EuclN => (0 : ℝ)) := by
    have h_restrict_eq :
        ((volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) γ)).restrict
          (chartPouKernel (I := I) (M := M) γ)ᶜ =
        (volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) γ \
            chartPouKernel (I := I) (M := M) γ) := by
      rw [Measure.restrict_restrict hK_meas.compl, Set.inter_comm,
        ← Set.diff_eq]
    rw [h_restrict_eq]
    exact h_off_raw
  have h_off_K : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) γ)),
      y ∉ chartPouKernel (I := I) (M := M) γ →
        eigenvectorChartComponentFun (I := I) (M := M) g r s i γ Q y =
          chartKernelCutoffPushed (I := I) (M := M) γ y *
            eigenvectorChartComponentFun (I := I) (M := M)
              g r s i γ Q y := by
    have h_imp := (ae_restrict_iff' hK_meas.compl).mp h_off_restrict
    filter_upwards [h_imp] with y hy hy_off
    have hy_zero : eigenvectorChartComponentFun (I := I) (M := M)
        g r s i γ Q y = 0 := hy hy_off
    rw [hy_zero, mul_zero]
  filter_upwards [h_on_K, h_off_K] with y hy_on hy_off
  by_cases hy_mem : y ∈ chartPouKernel (I := I) (M := M) γ
  · exact hy_on hy_mem
  · exact hy_off hy_mem

omit [CompleteSpace E] in
private lemma chosenComp_comp_chartTransition_ae_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β γ : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => chosenComp (I := I) (M := M) g r s i γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y))
      =ᵐ[(volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ)]
      (fun y => eigenvectorChartComponentFun (I := I) (M := M)
        g r s i γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y)) := by
  have h_target := chosenComp_ae_eq (I := I) (M := M) g r s i γ Q
  have h_overlap :
      chosenComp (I := I) (M := M) g r s i γ Q
        =ᵐ[(volume : Measure EuclN).restrict
            (chartOverlapEuclid (I := I) (M := M) γ β)]
        eigenvectorChartComponentFun (I := I) (M := M) g r s i γ Q :=
    ae_mono (Measure.restrict_mono_set _
      (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) γ β)) h_target
  exact chartTransitionEuclid_comp_ae_eq_restrict (I := I) (M := M) β γ h_overlap

omit [CompleteSpace E] in
private lemma eigenvectorChartComponentFun_comp_chartTransition_ae_eq_cutoff_mul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β γ : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => eigenvectorChartComponentFun (I := I) (M := M)
        g r s i γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y))
      =ᵐ[(volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ)]
      (fun y => chartKernelCutoffPushed (I := I) (M := M) γ
          (chartTransitionEuclid (I := I) (M := M) β γ y) *
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s i γ Q
          (chartTransitionEuclid (I := I) (M := M) β γ y)) := by
  have h_target :=
    eigenvectorChartComponentFun_ae_eq_chartKernelCutoffPushed_mul
      (I := I) (M := M) g r s i γ Q
  have h_overlap :
      eigenvectorChartComponentFun (I := I) (M := M) g r s i γ Q
        =ᵐ[(volume : Measure EuclN).restrict
            (chartOverlapEuclid (I := I) (M := M) γ β)]
        (fun y => chartKernelCutoffPushed (I := I) (M := M) γ y *
          eigenvectorChartComponentFun (I := I) (M := M)
            g r s i γ Q y) :=
    ae_mono (Measure.restrict_mono_set _
      (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) γ β)) h_target
  exact chartTransitionEuclid_comp_ae_eq_restrict (I := I) (M := M) β γ h_overlap

open Classical in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorSmoothChart_transport_term_aeEq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β γ : M) (P₀ Q : TensorCompIdx (E := E) r s) :
    (fun y => chartPushedRaw I β
        (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
      chartPushedRaw I β
        (fun x => if x ∈ (chartAt H γ).source then
          transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q x *
            tensorChartComponentRaw (I := I) (M := M) g r s
              (eigenvectorSmoothChart (I := I) (M := M) g r s i γ)
              γ Q.1 Q.2 x
          else 0) y)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
    (fun y => chartPushedRaw I β
        (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y *
      ((chartTransitionTransportCLM (I := I) (M := M) g r s γ β P₀ Q
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) γ Q) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
  classical
  set W : EuclN → ℝ := fun y => chartPushedRaw I β
    (fun x => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) y with hW_def
  set A : EuclN → ℝ := fun y => chartPushedRaw I β
    (fun x => if x ∈ (chartAt H γ).source then
      transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q x *
        tensorChartComponentRaw (I := I) (M := M) g r s
          (eigenvectorSmoothChart (I := I) (M := M) g r s i γ)
          γ Q.1 Q.2 x
      else 0) y with hA_def
  set B : EuclN → ℝ := fun y =>
    ((chartTransitionTransportCLM (I := I) (M := M) g r s γ β P₀ Q
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) γ Q) :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y with hB_def
  set RHS : EuclN → ℝ := fun y =>
    chartPushedRaw (I := I) (M := M) β
        (transportCoeffManifold (I := I) (M := M) g r s γ β P₀ Q) y *
      eigenvectorChartComponentFun (I := I) (M := M) g r s i γ Q
        (chartTransitionEuclid (I := I) (M := M) β γ y) with hRHS_def
  have hB_eq : B =ᵐ[chartL2Measure (I := I) (M := M) β] RHS := by
    have h := chartTransitionTransportCLM_coeFn_aeEq (I := I) (M := M) g r s γ β
      P₀ Q (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) γ Q)
    exact h.trans (Filter.EventuallyEq.of_eq rfl)
  have h_goal : (fun y => W y * A y)
      =ᵐ[chartL2Measure (I := I) (M := M) β] (fun y => W y * RHS y) := by
    have hΩ_open : IsOpen (chartOverlapEuclid (I := I) (M := M) β γ) :=
      chartOverlapEuclid_isOpen (I := I) (M := M) β γ
    have hΩ_meas : MeasurableSet (chartOverlapEuclid (I := I) (M := M) β γ) :=
      hΩ_open.measurableSet
    have h_restrict_eq :
        (chartL2Measure (I := I) (M := M) β).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ) =
        (volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ) := by
      rw [chartL2Measure, Measure.restrict_restrict hΩ_meas,
        Set.inter_eq_left.mpr
          (chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β γ)]
    have h_on_overlap : (fun y => W y * A y)
        =ᵐ[(chartL2Measure (I := I) (M := M) β).restrict
            (chartOverlapEuclid (I := I) (M := M) β γ)]
        (fun y => W y * RHS y) := by
      rw [h_restrict_eq]
      have h_mem : ∀ᵐ y ∂((volume : Measure EuclN).restrict
          (chartOverlapEuclid (I := I) (M := M) β γ)),
          y ∈ chartOverlapEuclid (I := I) (M := M) β γ :=
        ae_restrict_mem hΩ_meas
      have h_cc := chosenComp_comp_chartTransition_ae_eq
        (I := I) (M := M) g r s i β γ Q
      have h_kc :=
        eigenvectorChartComponentFun_comp_chartTransition_ae_eq_cutoff_mul
          (I := I) (M := M) g r s i β γ Q
      filter_upwards [h_mem, h_cc, h_kc] with y hy_mem hy_cc hy_kc
      have hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β :=
        chartOverlapEuclid_subset_chartTarget (I := I) (M := M) β γ hy_mem
      set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
        with hz_def
      have hz_srcβ : z ∈ (chartAt H β).source :=
        symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) β hy_target
      have hz_srcγ : z ∈ (chartAt H γ).source :=
        (mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
          (I := I) (M := M) β γ hy_target).mp hy_mem
      set zγ : EuclN := (toEuclidean (E := E)) (extChartAt I γ z) with hzγ_def
      have hsymm_target : (toEuclidean (E := E)).symm y ∈
          (extChartAt I β).target := by
        rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy_target
        exact hy_target
      have hy_eq : (toEuclidean (E := E)) (extChartAt I β z) = y := by
        rw [hz_def, (extChartAt I β).right_inv hsymm_target]
        exact (toEuclidean (E := E)).apply_symm_apply y
      have hT_eq : chartTransitionEuclid (I := I) (M := M) β γ y = zγ := by
        rw [← hy_eq, hzγ_def]
        exact chartTransitionEuclid_eq_chartα_image (I := I) (M := M) β γ hz_srcβ
      have hA_y : A y =
          transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z *
            chosenComp (I := I) (M := M) g r s i γ Q zγ := by
        rw [hA_def]
        simp only
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
          ← hz_def, if_pos hz_srcγ]
        congr 1
        have h_raw := tensorChartComponentRaw_eigenvectorSmoothChart_self
          (I := I) (M := M) g r s i γ Q
          (toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) γ
            hz_srcγ)
        rw [symm_toEuclidean_symm_toEuclidean_extChartAt
          (I := I) (M := M) γ hz_srcγ] at h_raw
        rw [h_raw, hzγ_def]
      have hRHS_y : RHS y =
          (((chartKernelCutoff (I := I) (M := M) β :
                C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
            ((chartKernelCutoff (I := I) (M := M) γ :
                C^∞⟮I, M; ℝ⟯) : M → ℝ) z *
            transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z) *
          eigenvectorChartComponentFun (I := I) (M := M)
            g r s i γ Q zγ := by
        rw [hRHS_def]
        simp only
        rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
          ← hz_def, transportCoeffManifold_apply, hT_eq]
      have h_cutγ : chartKernelCutoffPushed (I := I) (M := M) γ zγ =
          ((chartKernelCutoff (I := I) (M := M) γ : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
        rw [hzγ_def]
        exact chartKernelCutoffPushed_toEuclidean_extChartAt
          (I := I) (M := M) γ hz_srcγ
      rw [hT_eq] at hy_cc hy_kc
      rw [h_cutγ] at hy_kc
      set Eγ : ℝ := eigenvectorChartComponentFun (I := I) (M := M)
        g r s i γ Q zγ with hEγ_def
      rw [hA_y, hy_cc, hRHS_y]
      by_cases hWy : W y = 0
      · rw [hWy, zero_mul, zero_mul]
      · have hWy_val : W y =
            ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) z := by
          rw [hW_def]
          simp only
          rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
            ← hz_def]
        have hz_pou : z ∈ tsupport
            (fun x : M => ((chartAtlasPOU I M β : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
          refine subset_tsupport _ ?_
          rw [Function.mem_support]
          rw [hWy_val] at hWy
          exact hWy
        have h_cutβ : ((chartKernelCutoff (I := I) (M := M) β :
            C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 1 :=
          chartKernelCutoff_eqOn_one (I := I) (M := M) β hz_pou
        rw [h_cutβ, one_mul]
        rw [show transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z * Eγ =
            transitionCoeff (E := E) (I := I) (M := M) r s γ β P₀ Q z *
              (((chartKernelCutoff (I := I) (M := M) γ :
                  C^∞⟮I, M; ℝ⟯) : M → ℝ) z * Eγ) from by rw [← hy_kc]]
        ring
    have h_off_overlap : ∀ y, y ∉ chartOverlapEuclid (I := I) (M := M) β γ →
        W y * A y = W y * RHS y := by
      intro y hy_notin
      by_cases hy_target : y ∈ chartTargetEuclid (I := I) (M := M) β
      · set z : M := (extChartAt I β).symm ((toEuclidean (E := E)).symm y)
          with hz_def
        have hz_notin_srcγ : z ∉ (chartAt H γ).source := by
          intro hz_srcγ
          exact hy_notin
            ((mem_chartOverlapEuclid_iff_of_mem_chartTargetEuclid
              (I := I) (M := M) β γ hy_target).mpr hz_srcγ)
        have hA_y : A y = 0 := by
          rw [hA_def]
          simp only
          rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
            ← hz_def, if_neg hz_notin_srcγ]
        have hRHS_y : RHS y = 0 := by
          rw [hRHS_def]
          simp only
          have h_cutγ_zero : ((chartKernelCutoff (I := I) (M := M) γ :
              C^∞⟮I, M; ℝ⟯) : M → ℝ) z = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h =>
              hz_notin_srcγ
                (chartKernelCutoff_tsupport_subset_source (I := I) (M := M) γ h))
          have h_coeff_zero : chartPushedRaw (I := I) (M := M) β
              (transportCoeffManifold (I := I) (M := M) g r s γ β P₀ Q) y = 0 := by
            rw [chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hy_target,
              ← hz_def, transportCoeffManifold_apply, h_cutγ_zero]
            ring
          rw [h_coeff_zero, zero_mul]
        rw [hA_y, hRHS_y]
      · have hWy : W y = 0 := by
          rw [hW_def]
          simp only
          exact chartPushedRaw_apply_of_notMem (I := I) (M := M) β _ hy_target
        rw [hWy, zero_mul, zero_mul]
    exact ae_eq_of_ae_eq_restrict_of_eqOn_compl hΩ_meas h_on_overlap
      h_off_overlap
  refine h_goal.trans ?_
  exact (Filter.EventuallyEq.refl _ W).mul hB_eq.symm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
