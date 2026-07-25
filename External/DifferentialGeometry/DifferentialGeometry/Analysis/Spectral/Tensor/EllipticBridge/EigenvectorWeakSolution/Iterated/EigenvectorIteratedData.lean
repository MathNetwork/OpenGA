import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Iterated.EigenvectorIteratedRegularity
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.DifferentiatedRHS.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.VariationalIdentity.EigenvectorLeibnizCommutator
import DifferentialGeometry.Analysis.Sobolev.Euclidean.SupportAndDomain.IteratedSobolevSupportPromotion


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartH2NonSmooth
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearUniformDiffQuotBoundCanonical
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Chart hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma chartTargetEuclid_sdiff_chartPouKernel_isOpen (α : M) :
    IsOpen (chartTargetEuclid (I := I) (M := M) α \
      chartPouKernel (I := I) (M := M) α) :=
  (DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
    (chartPouKernel_isCompact (I := I) (M := M) α).isClosed

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] in
private lemma chartTargetEuclid_sdiff_chartPouKernel_subset (α : M) :
    chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α ⊆
      chartTargetEuclid (I := I) (M := M) α :=
  Set.diff_subset

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
lemma chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
    (α : M) {u : EuclN → ℝ}
    (hu_ae : u =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ => (0 : ℝ)))
    (i : Fin (Module.finrank ℝ E)) :
    chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u
        (chartTargetEuclid (I := I) (M := M) α)
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartPouKernel (I := I) (M := M) α with hV_def
  have hΩ_open : IsOpen Ω := DifferentialGeometry.Analysis.Laplacian.MetricExtension.chartTargetEuclid_isOpen (I := I) (M := M) α
  have hV_open : IsOpen V :=
    chartTargetEuclid_sdiff_chartPouKernel_isOpen (I := I) (M := M) α
  have hV_sub : V ⊆ Ω := chartTargetEuclid_sdiff_chartPouKernel_subset (I := I) (M := M) α
  by_cases hW : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u Ω
  · have hu_V : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u V := by
      refine ⟨hW.1.mono_measure (Measure.restrict_mono_set _ hV_sub), ?_⟩
      intro j
      obtain ⟨gj, hgj_memLp, hgj_weak⟩ := hW.2 j
      exact ⟨gj, hgj_memLp.mono_measure (Measure.restrict_mono_set _ hV_sub),
        DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_sub hgj_weak⟩
    have h_chosen_V_zero :
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u V
          =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) :=
      chosenWeakPartial'_ae_zero_of_ae_zero (d := Module.finrank ℝ E)
        (by norm_num) hV_open hu_ae i
    have h_partial_Ω : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) u Ω :=
      chosenWeakPartial'_isWeakPartial_of_mem hW i
    have h_partial_Ω_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω) u V :=
      DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_sub h_partial_Ω
    have h_partial_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u V) u V :=
      chosenWeakPartial'_isWeakPartial_of_mem hu_V i
    have hLp_Ω_V : LocallyIntegrable
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω)
        ((volume : Measure EuclN).restrict V) :=
      ((chosenWeakPartial'_memLp_of_mem hW i).mono_measure
        (Measure.restrict_mono_set _ hV_sub)).locallyIntegrable (by norm_num)
    have hLp_V : LocallyIntegrable
        (chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u V)
        ((volume : Measure EuclN).restrict V) :=
      (chosenWeakPartial'_memLp_of_mem hu_V i).locallyIntegrable (by norm_num)
    have h_eq : chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u Ω
        =ᵐ[(volume : Measure EuclN).restrict V]
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 i u V :=
      DeGiorgi.HasWeakPartialDeriv.ae_eq hV_open h_partial_Ω_V h_partial_V
        hLp_Ω_V hLp_V
    exact h_eq.trans h_chosen_V_zero
  · rw [chosenWeakPartial'_of_not_mem hW]
    exact Filter.Eventually.of_forall (fun _ => rfl)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
lemma eigenvectorChartWeakPartial_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    eigenvectorChartWeakPartial (I := I) (M := M) g r s i α P₀ k
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartPouKernel (I := I) (M := M) α with hV_def
  have hV_open : IsOpen V :=
    chartTargetEuclid_sdiff_chartPouKernel_isOpen (I := I) (M := M) α
  have hV_sub : V ⊆ Ω :=
    chartTargetEuclid_sdiff_chartPouKernel_subset (I := I) (M := M) α
  have hV_meas : MeasurableSet V := hV_open.measurableSet
  set uVec :=
    tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i
    with huVec_def
  have h_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ chartPouKernel (I := I) (M := M) α →
        (tensorL2ChartComponent (I := I) (M := M) g r s uVec α P₀ :
          EuclN → ℝ) y = 0 :=
    tensorL2ChartComponent_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s uVec α P₀
  have h_ae_V : ∀ᵐ y ∂((volume : Measure EuclN).restrict V),
      y ∉ chartPouKernel (I := I) (M := M) α →
        (tensorL2ChartComponent (I := I) (M := M) g r s uVec α P₀ :
          EuclN → ℝ) y = 0 :=
    ae_mono (Measure.restrict_mono_set _ hV_sub) h_ae
  have hu_ae : (tensorL2ChartComponent (I := I) (M := M) g r s uVec α P₀ :
        EuclN → ℝ)
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
    filter_upwards [(ae_restrict_iff' hV_meas).mp h_ae_V] with y hy
    intro hy_V
    exact hy hy_V hy_V.2
  have h_wp_Ω : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i α P₀ k)
      (tensorL2ChartComponent (I := I) (M := M) g r s uVec α P₀)
      Ω :=
    eigenvectorChartWeakPartial_hasWeakPartialDeriv
      (I := I) (M := M) g r s i α P₀ k
  have h_wp_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i α P₀ k)
      (tensorL2ChartComponent (I := I) (M := M) g r s uVec α P₀)
      V :=
    DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_sub h_wp_Ω
  have h_zero_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (fun _ : EuclN => (0 : ℝ))
      (tensorL2ChartComponent (I := I) (M := M) g r s uVec α P₀) V := by
    intro φ hφ hφ_supp hφ_sub
    have h_ae_lhs :
        (fun x : EuclN =>
            (tensorL2ChartComponent (I := I) (M := M) g r s uVec α P₀ :
              EuclN → ℝ) x *
            (fderiv ℝ φ x) (EuclideanSpace.single k 1))
          =ᵐ[(volume : Measure EuclN).restrict V]
        (fun x : EuclN => (0 : ℝ) *
            (fderiv ℝ φ x) (EuclideanSpace.single k 1)) := by
      filter_upwards [hu_ae] with x hx
      simp [hx]
    rw [integral_congr_ae h_ae_lhs]
    simp
  have h_wp_memLp_Ω : MemLp
      (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i α P₀ k) 2
      ((volume : Measure EuclN).restrict Ω) :=
    Lp.memLp (eigenvectorChartPartialLp (I := I) (M := M)
      g r s i α P₀ k)
  have h_wp_loc : MeasureTheory.LocallyIntegrable
      (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i α P₀ k)
      ((volume : Measure EuclN).restrict V) :=
    (h_wp_memLp_Ω.mono_measure (Measure.restrict_mono_set _ hV_sub)).locallyIntegrable
      (by norm_num)
  have h_zero_loc : MeasureTheory.LocallyIntegrable (fun _ : EuclN => (0 : ℝ))
      ((volume : Measure EuclN).restrict V) :=
    MeasureTheory.locallyIntegrable_const 0
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hV_open h_wp_V h_zero_V
    h_wp_loc h_zero_loc

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
lemma eigenvectorChartComponentFun_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  have h_ae : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α P₀ y = 0 :=
    tensorL2ChartComponent_ae_zero_off_chartPouKernel
      (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M)
          g r s) i) α P₀
  have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \
      chartPouKernel (I := I) (M := M) α) :=
    (chartTargetEuclid_sdiff_chartPouKernel_isOpen (I := I) (M := M) α).measurableSet
  have h_ae_V : ∀ᵐ y ∂((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartPouKernel (I := I) (M := M) α)),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s i α P₀ y = 0 :=
    ae_mono (Measure.restrict_mono_set _
      (chartTargetEuclid_sdiff_chartPouKernel_subset (I := I) (M := M) α)) h_ae
  rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
  filter_upwards [(ae_restrict_iff' hV_meas).mp h_ae_V] with y hy
  intro hy_V
  exact hy hy_V hy_V.2

omit [CompleteSpace E] in
lemma eigenvectorChartIteratedPartial_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)) :
    eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s i α P₀ m l
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  induction m with
  | zero =>
      rw [eigenvectorChartIteratedPartial_zero]
      exact eigenvectorChartComponentFun_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀
  | succ m ih =>
      rw [eigenvectorChartIteratedPartial_succ]
      exact chosenWeakPartial'_ae_zero_off_chartPouKernel_of_ae_zero
        α (ih (Fin.init l)) (l (Fin.last m))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma crossLeftTestCoeff_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (Q : TensorCompIdx (E := E) r (s + 1))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y = 0 := by
  rw [crossLeftTestCoeff_def,
    euclidPartial_chartPushedRaw_pou_eq_zero_off_chartPouKernel
      (I := I) (M := M) α (Q.2 0) hy, zero_mul]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma gradChartCoeffEuclid_pou_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (α : M)
    (m : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    gradChartCoeffEuclid (I := I) (M := M) g α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) m y = 0 := by
  classical
  rw [gradChartCoeffEuclid]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [euclidPartial_chartPushedRaw_pou_eq_zero_off_chartPouKernel
    (I := I) (M := M) α j hy, mul_zero]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
lemma crossRightTestValueCoeff_eq_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s) (Q : TensorCompIdx (E := E) r s)
    {y : EuclN} (hy : y ∉ chartPouKernel (I := I) (M := M) α) :
    crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y = 0 := by
  classical
  rw [crossRightTestValueCoeff_def]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  rw [gradChartCoeffEuclid_pou_eq_zero_off_chartPouKernel
    (I := I) (M := M) g α m hy, zero_mul]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
lemma eigenvectorChartRHS_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    eigenvectorChartRHS (I := I) (M := M) g r s i α P₀
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  classical
  set V : Set EuclN := chartTargetEuclid (I := I) (M := M) α \
    chartPouKernel (I := I) (M := M) α with hV_def
  have hV_meas : MeasurableSet V :=
    (chartTargetEuclid_sdiff_chartPouKernel_isOpen (I := I) (M := M) α).measurableSet
  have h_comp := eigenvectorChartComponentFun_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s i α P₀
  rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
  filter_upwards [(ae_restrict_iff' hV_meas).mp h_comp] with y h_comp_y
  intro hy_V
  have hy : y ∉ chartPouKernel (I := I) (M := M) α := hy_V.2
  have h_comp_zero : eigenvectorChartComponentFun (I := I) (M := M)
      g r s i α P₀ y = 0 := h_comp_y hy_V
  rw [eigenvectorChartRHS]
  have h_crossLeft :
      (∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) = 0 := by
    refine Finset.sum_eq_zero (fun P _ => Finset.sum_eq_zero (fun Q _ => ?_))
    rw [crossLeftTestCoeff_eq_zero_off_chartPouKernel
      (I := I) (M := M) g r s α P₀ Q hy, mul_zero, zero_mul]
  have h_crossRight :
      (∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) = 0 := by
    refine Finset.sum_eq_zero (fun P _ => Finset.sum_eq_zero (fun Q _ => ?_))
    rw [crossRightTestValueCoeff_eq_zero_off_chartPouKernel
      (I := I) (M := M) g r s α P₀ Q hy, mul_zero, zero_mul]
  rw [show ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α P₀ :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0
    from h_comp_zero,
    h_crossLeft, h_crossRight,
    covPrincipalRotationCoeffLimit_eq_zero_off_chartPouKernel_unconditional
      (I := I) (M := M) g r s i α P₀ hy,
    covLowerOrderRotationValueCoeffLimit_eq_zero_off_chartPouKernel_unconditional
      (I := I) (M := M) g r s i α P₀ hy,
    crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
      (I := I) (M := M) g r s i α P₀ hy]
  rw [Finset.sum_eq_zero (fun l _ =>
    weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel_unconditional
      (I := I) (M := M) g r s i α P₀ l hy)]
  ring

private lemma thickening_mono_of_lt
    {β : Type*} [PseudoEMetricSpace β]
    {ρ ρ' : ℝ} (hρ_lt : ρ < ρ') (K : Set β) :
    Metric.thickening ρ K ⊆ Metric.thickening ρ' K := by
  intro y hy
  refine Metric.mem_thickening_iff_infEDist_lt.mpr ?_
  exact lt_of_lt_of_le (Metric.mem_thickening_iff_infEDist_lt.mp hy)
    (ENNReal.ofReal_le_ofReal hρ_lt.le)

omit [CompleteSpace E] in
private lemma tensorChartBilinear_uniform_diffQuot_bound_of_data
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    ∃ M_bound : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ,
      (∀ j k, 0 ≤ M_bound j k) ∧
      (∀ (j k : Fin (Module.finrank ℝ E)) (h : ℝ),
        0 < |h| → |h| ≤ R₀ / 16 →
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.diffQuot
              (d := Module.finrank ℝ E) k h (D.weak_partial j)) 2
            ((volume : Measure EuclN).restrict Ω'')
          ≤ ENNReal.ofReal (M_bound j k)) := by
  classical
  set K_α : Set EuclN := closure Ω'' with hK_α_def
  have hK_α_compact : IsCompact K_α := hΩ''_compact_closure
  set ε : ℝ := R₀ / 16 with hε_def
  have hε_pos : 0 < ε := by positivity
  set Ω' : Set EuclN := Metric.thickening (8 * ε) K_α with hΩ'_def
  have hΩ'_open : IsOpen Ω' := Metric.isOpen_thickening
  have h_closureΩ'_sub : closure Ω' ⊆ Metric.cthickening (8 * ε) K_α :=
    closure_minimal (Metric.thickening_subset_cthickening _ _)
      Metric.isClosed_cthickening
  have h_cthick_eight_ε_in_chart : Metric.cthickening (8 * ε) K_α ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    have hle : (8 * ε) ≤ R₀ := by change 8 * (R₀ / 16) ≤ R₀; linarith
    exact (Metric.cthickening_mono hle K_α).trans h_room
  have h_closureΩ'_in_chart :
      closure Ω' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    h_closureΩ'_sub.trans h_cthick_eight_ε_in_chart
  have hΩ'_compact_closure : IsCompact (closure Ω') :=
    hK_α_compact.cthickening.of_isClosed_subset isClosed_closure h_closureΩ'_sub
  set K_η : Set EuclN := Metric.cthickening (3 * ε) K_α with hK_η_def
  have hK_η_compact : IsCompact K_η := hK_α_compact.cthickening
  set Ω_η : Set EuclN := Metric.thickening (5 * ε) K_α with hΩ_η_def
  have hΩ_η_open : IsOpen Ω_η := Metric.isOpen_thickening
  have hK_η_in_Ω_η : K_η ⊆ Ω_η :=
    Metric.cthickening_subset_thickening' (by positivity) (by linarith) K_α
  obtain ⟨_δ_η, η, _hδ_η_pos, _hδ_η_sub_Ωη, hη_smooth, hη_supp, hη_range,
      hη_one_on_cthick_K_η, hη_tsupp_in_Ω_η⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      (d := Module.finrank ℝ E) hK_η_compact hΩ_η_open hK_η_in_Ω_η
  obtain ⟨N, hN_pos, h_fderiv_eta⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.exists_grad_bound_of_compactSupport_smooth
      hη_smooth hη_supp
  have hN_nn : 0 ≤ N := hN_pos.le
  have hη_one_on_K_η : ∀ x ∈ K_η, η x = 1 := fun x hx =>
    hη_one_on_cthick_K_η x (Metric.self_subset_cthickening _ hx)
  have hΩ''_sub_K_η : Ω'' ⊆ K_η := by
    intro y hy
    exact Metric.self_subset_cthickening _ (subset_closure hy)
  have hη_one_on_Ω'' : ∀ x ∈ Ω'', η x = 1 :=
    fun x hx => hη_one_on_K_η x (hΩ''_sub_K_η hx)
  have hη_in_Ω' : tsupport η ⊆ Ω' := by
    refine hη_tsupp_in_Ω_η.trans ?_
    rw [hΩ_η_def, hΩ'_def]
    exact thickening_mono_of_lt (by linarith) K_α
  have hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ ε →
      Metric.cthickening |h| (tsupport η) ⊆ Ω' := by
    intro h hh
    have h_tsupp_in_cthick_5ε : tsupport η ⊆ Metric.cthickening (5 * ε) K_α := by
      refine hη_tsupp_in_Ω_η.trans ?_
      rw [hΩ_η_def]
      exact Metric.thickening_subset_cthickening _ _
    by_cases h_abs : |h| ≤ 0
    · have hh_zero : |h| = 0 := le_antisymm h_abs (abs_nonneg _)
      have hcth_zero : Metric.cthickening |h| (tsupport η) = tsupport η := by
        rw [hh_zero, Metric.cthickening_zero]
        exact (isClosed_tsupport η).closure_eq
      rw [hcth_zero]; exact hη_in_Ω'
    · have h_abs_pos : 0 < |h| := not_le.mp h_abs
      have h1 : Metric.cthickening |h| (tsupport η) ⊆
          Metric.cthickening |h| (Metric.cthickening (5 * ε) K_α) :=
        Metric.cthickening_subset_of_subset _ h_tsupp_in_cthick_5ε
      have h2 : Metric.cthickening |h| (Metric.cthickening (5 * ε) K_α) ⊆
          Metric.cthickening (|h| + 5 * ε) K_α :=
        Metric.cthickening_cthickening_subset h_abs_pos.le (by positivity) K_α
      have h_le : |h| + 5 * ε < 8 * ε := by nlinarith [hε_pos]
      have h3 : Metric.cthickening (|h| + 5 * ε) K_α ⊆ Ω' := by
        rw [hΩ'_def]
        exact Metric.cthickening_subset_thickening' (by linarith) h_le K_α
      exact (h1.trans h2).trans h3
  obtain ⟨M_bound, hM_nn, h_bd⟩ :=
    chartBilinearH1Compl_uniform_diffQuot_bound_of_data
      (I := I) (M := M) (g := g) (α := α) D.toChartData
      hη_smooth hη_supp hη_range hN_nn h_fderiv_eta
      hΩ'_open h_closureΩ'_in_chart hΩ'_compact_closure
      hη_in_Ω' hε_pos hh_supp_in_Ω' hη_one_on_Ω'' hΩ''_open.measurableSet
  refine ⟨M_bound, hM_nn, fun j k h hh_pos hh_le => ?_⟩
  exact h_bd j k h hh_pos (by rw [hε_def] at *; linarith)

omit [CompleteSpace E] in
lemma tensorChartBilinear_chartComponent_regularity_of_data
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {α : M}
    {P₀ : TensorCompIdx (E := E) r s}
    (D : TensorChartBilinearH1ComplData (I := I) (M := M) g r s α P₀)
    {Ω'' : Set EuclN} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {R₀ : ℝ} (hR₀_pos : 0 < R₀)
    (h_room : Metric.cthickening R₀ (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 D.u_chart Ω'' ∧
      (∀ j, DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 (D.weak_partial j) Ω'') := by
  classical
  have h_closureΩ''_in_chart :
      closure Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    fun x hx => h_room (Metric.self_subset_cthickening _ hx)
  have hΩ''_in_chart : Ω'' ⊆ chartTargetEuclid (I := I) (M := M) α :=
    fun y hy => h_closureΩ''_in_chart (subset_closure hy)
  set R_dq : ℝ := R₀ / 16 with hR_dq_def
  have hR_dq_pos : 0 < R_dq := by positivity
  have h_room_dq : Metric.cthickening R_dq (closure Ω'') ⊆
      chartTargetEuclid (I := I) (M := M) α :=
    (Metric.cthickening_mono (by rw [hR_dq_def]; linarith) (closure Ω'')).trans h_room
  obtain ⟨M_bound, hM_nn, h_uniform_bd⟩ :=
    tensorChartBilinear_uniform_diffQuot_bound_of_data
      (g := g) (r := r) (s := s) (α := α) (P₀ := P₀) D
      hΩ''_open hΩ''_compact_closure hR₀_pos h_room
  have h_h2 :=
    tensor_h2_chart_loc_of_uniform_bound (I := I) (M := M)
      (g := g) (r := r) (s := s) (α := α) (P₀ := P₀) D
      hΩ''_open hΩ''_compact_closure hR_dq_pos h_room_dq hM_nn h_uniform_bd
  have h_dwp_memLp_Ω'' :
      ∀ j, MemLp (D.weak_partial j) 2 ((volume : Measure EuclN).restrict Ω'') :=
    fun j => (D.weak_partial_locally_memLp j hΩ''_compact_closure
      h_closureΩ''_in_chart).mono_measure
        (Measure.restrict_mono subset_closure le_rfl)
  have h_dwp_weak_uChart_Ω'' :
      ∀ j, DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) j
        (D.weak_partial j) D.u_chart Ω'' :=
    fun j => DeGiorgi.HasWeakPartialDeriv.restrict hΩ''_open hΩ''_in_chart
      (D.weak_partial_isWeakPartial j)
  have h_uChart_memLp_Ω'' :
      MemLp D.u_chart 2 ((volume : Measure EuclN).restrict Ω'') :=
    (D.memLp_volume_restrict_u_chart hΩ''_compact_closure
      hΩ''_compact_closure.isClosed.measurableSet h_closureΩ''_in_chart).mono_measure
        (Measure.restrict_mono subset_closure le_rfl)
  have h_uChart_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      D.u_chart Ω'' :=
    ⟨h_uChart_memLp_Ω'', fun j =>
      ⟨D.weak_partial j, h_dwp_memLp_Ω'' j, h_dwp_weak_uChart_Ω'' j⟩⟩
  refine ⟨h_uChart_memW1p, fun j => ⟨h_dwp_memLp_Ω'' j, fun k => ?_⟩⟩
  obtain ⟨g_jk, hg_jk_memLp, hg_jk_partial, _hg_jk_norm⟩ := h_h2 j k
  exact ⟨g_jk, hg_jk_memLp, hg_jk_partial⟩

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
