import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.RHS.ChartRHSBounds.EigenvectorChartRHS
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.CovGrad.EigenvectorCovGradComponent
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Cutoff.EigenvectorCutoffWeakPartials


noncomputable section

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma memWkp_finsetSum
    {d : ℕ} [NeZero d] {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {ι : Type*} (T : Finset ι)
    (F : ι → EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ i ∈ T, MemWkp (d := d) k p (F i) Ω) :
    MemWkp (d := d) k p (fun y => ∑ i ∈ T, F i y) Ω := by
  classical
  induction T using Finset.induction with
  | empty =>
      simpa using MemWkp_zero_fun (d := d) (k := k) (p := p) hp hΩ
  | insert a s ha ih =>
      have hF_a : MemWkp (d := d) k p (F a) Ω :=
        hF a (Finset.mem_insert_self a s)
      have hF_s : ∀ i ∈ s, MemWkp (d := d) k p (F i) Ω :=
        fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have h_sum_s : MemWkp (d := d) k p (fun y => ∑ i ∈ s, F i y) Ω := ih hF_s
      have h_add : MemWkp (d := d) k p
          (fun y => F a y + ∑ i ∈ s, F i y) Ω :=
        MemWkp.add (d := d) hp hΩ hF_a h_sum_s
      have h_eq : (fun y => ∑ i ∈ insert a s, F i y) =
          fun y => F a y + ∑ i ∈ s, F i y := by
        funext y
        rw [Finset.sum_insert ha]
      rw [h_eq]
      exact h_add

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma memWkp_smoothCoef_mul_aeZeroFactor
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    {Kkern : Set EuclN}
    (hKkern_compact : IsCompact Kkern)
    (hKkern_in : Kkern ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ Kkern → factor y = 0) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  obtain ⟨δ, χ, hδ_pos, hδ_in, hχ_smooth, hχ_cs, _hχ_range, hχ_one, hχ_tsupp⟩ :=
    exists_smooth_cutoff_with_neighborhood (d := Module.finrank ℝ E)
      hKkern_compact hΩ_open hKkern_in
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
  set Cδ : Set EuclN := Metric.cthickening δ Kkern with hCδ_def
  have hCδ_closed : IsClosed Cδ := Metric.isClosed_cthickening
  have hCδ_meas : MeasurableSet Cδ := hCδ_closed.measurableSet
  have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kkern → factor y = 0 := by
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
  have hKkern_in_Cδ : Kkern ⊆ Cδ := Metric.self_subset_cthickening _
  have h_eq_on_diff : (fun y => (χ y * coef y) * factor y)
      =ᵐ[(volume : Measure EuclN).restrict (Ω \ Cδ)]
      (fun y => coef y * factor y) := by
    have h_diff_in_Ω : (volume : Measure EuclN).restrict (Ω \ Cδ) ≤
        (volume : Measure EuclN).restrict Ω :=
      Measure.restrict_mono Set.diff_subset le_rfl
    have h_factor_diff : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
        factor y = 0 := by
      have h_lift : ∀ᵐ y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          y ∉ Kkern → factor y = 0 :=
        (Measure.absolutelyContinuous_of_le h_diff_in_Ω).ae_le hfactor_ae_zero'
      have h_off : ∀ᵐ _y ∂((volume : Measure EuclN).restrict (Ω \ Cδ)),
          _y ∈ Ω \ Cδ := ae_restrict_mem (hΩ_meas.diff hCδ_meas)
      filter_upwards [h_lift, h_off] with y hy hy_mem
      exact hy (fun hyK => hy_mem.2 (hKkern_in_Cδ hyK))
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

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma memWkp_of_weakPartial_of_memWkp_succ
    {K : ℕ} {Ω : Set EuclN} (hΩ : IsOpen Ω)
    (k : Fin (Module.finrank ℝ E))
    {gpart u : EuclN → ℝ}
    (hgpart_memLp : MemLp gpart 2 ((volume : Measure EuclN).restrict Ω))
    (hgpart_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      gpart u Ω)
    (hu : MemWkp (d := Module.finrank ℝ E) (K + 1) 2 u Ω) :
    MemWkp (d := Module.finrank ℝ E) K 2 gpart Ω := by
  classical
  have hu_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u Ω := hu.memW1p
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω) u Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_w1p k
  have h_chosen_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω) Ω :=
    hu.chosenWeakPartial_mem k
  have hgpart_loc : LocallyIntegrable gpart
      ((volume : Measure EuclN).restrict Ω) :=
    hgpart_memLp.locallyIntegrable (by norm_num)
  have h_chosen_loc : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω)
      ((volume : Measure EuclN).restrict Ω) :=
    h_chosen_memWkp.memLp.locallyIntegrable (by norm_num)
  have h_ae : gpart =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u Ω :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ hgpart_weak h_chosen_weak
      hgpart_loc h_chosen_loc
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ h_ae).mpr h_chosen_memWkp

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma hasWeakPartialDeriv_ae_zero_off_of_ae_zero_off
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    (k : Fin (Module.finrank ℝ E))
    {Kc : Set EuclN} (hKc_closed : IsClosed Kc)
    {gp u : EuclN → ℝ}
    (hgp_memLp : MemLp gp 2 ((volume : Measure EuclN).restrict Ω))
    (hgp_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      gp u Ω)
    (hu_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u Ω)
    (hu_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kc → u y = 0) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ Kc → gp y = 0 := by
  classical
  set V : Set EuclN := Ω \ Kc with hV_def
  have hV_open : IsOpen V := hΩ_open.sdiff hKc_closed
  have hV_sub : V ⊆ Ω := Set.diff_subset
  have hV_meas : MeasurableSet V := hV_open.measurableSet
  have hΩ_meas : MeasurableSet Ω := hΩ_open.measurableSet
  have hu_zero_V : u =ᵐ[(volume : Measure EuclN).restrict V]
      (fun _ : EuclN => (0 : ℝ)) := by
    have h_lift : ∀ᵐ y ∂((volume : Measure EuclN).restrict V),
        y ∉ Kc → u y = 0 :=
      (Measure.absolutelyContinuous_of_le
        (Measure.restrict_mono hV_sub le_rfl)).ae_le hu_zero
    have h_mem : ∀ᵐ y ∂((volume : Measure EuclN).restrict V), y ∈ V :=
      ae_restrict_mem hV_meas
    filter_upwards [h_lift, h_mem] with y hy hy_mem
    exact hy hy_mem.2
  have hu_w1p_V : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 u V :=
    MemW1p.mono_set hV_open hV_sub hu_w1p
  have h_chosen_zero : chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V
      =ᵐ[(volume : Measure EuclN).restrict V] (fun _ : EuclN => (0 : ℝ)) :=
    chosenWeakPartial'_ae_zero_of_ae_zero (d := Module.finrank ℝ E)
      (by norm_num) hV_open hu_zero_V k
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V) u V :=
    chosenWeakPartial'_isWeakPartial_of_mem hu_w1p_V k
  have hgp_weak_V : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      gp u V :=
    DeGiorgi.HasWeakPartialDeriv.restrict hV_open hV_sub hgp_weak
  have hgp_loc_V : LocallyIntegrable gp
      ((volume : Measure EuclN).restrict V) :=
    (hgp_memLp.mono_measure (Measure.restrict_mono hV_sub le_rfl)).locallyIntegrable
      (by norm_num)
  have h_chosen_loc_V : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V)
      ((volume : Measure EuclN).restrict V) :=
    (chosenWeakPartial'_memLp_of_mem hu_w1p_V k).locallyIntegrable (by norm_num)
  have h_gp_eq : gp =ᵐ[(volume : Measure EuclN).restrict V]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k u V :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hV_open hgp_weak_V h_chosen_weak
      hgp_loc_V h_chosen_loc_V
  have hgp_zero_V : gp =ᵐ[(volume : Measure EuclN).restrict V]
      (fun _ : EuclN => (0 : ℝ)) := h_gp_eq.trans h_chosen_zero
  have hgp_zero_V' : ∀ᵐ y ∂(volume : Measure EuclN),
      y ∈ V → gp y = 0 := by
    have h := (ae_restrict_iff' hV_meas).mp hgp_zero_V
    filter_upwards [h] with y hy hy_mem
    exact hy hy_mem
  refine (ae_restrict_iff' hΩ_meas).mpr ?_
  filter_upwards [hgp_zero_V'] with y hy hy_mem hy_notKc
  exact hy ⟨hy_mem, hy_notKc⟩

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
lemma eigenvectorCutoffChartComponent_memW1p
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  refine ⟨Lp.memLp _, fun k => ?_⟩
  refine ⟨((eigenvectorCutoffChartPartialLp (I := I) (M := M)
      g r s i α P k :
      Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ),
    Lp.memLp _, ?_⟩
  exact eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv
    (I := I) (M := M) g r s i α P k

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
lemma cutoffPartialLpLimit_ae_zero_off_cutoffChartKernelEuclid
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
        ((cutoffPartialLpLimit (I := I) (M := M) g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_smul : (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val •
        ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    rw [cutoffPartialLpLimit]
    exact Lp.coeFn_smul i.fst.val _
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv
      (I := I) (M := M) g r s i α P k
  have h_comp_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorCutoffChartComponent_memW1p (I := I) (M := M)
      g r s i α P
  have h_comp_zero := tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
      i) α P
  have h_partial_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
        ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
            g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 :=
    hasWeakPartialDeriv_ae_zero_off_of_ae_zero_off hΩ_open k
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α).isClosed
      (Lp.memLp _) h_weak h_comp_memW1p
      (by rw [← chartL2Measure]; exact h_comp_zero)
  filter_upwards [h_smul, h_partial_zero] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma memWkp_indicatorSmoothCoef_mul_aeZeroFactor
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    {Kkern : Set EuclN}
    (hKkern_compact : IsCompact Kkern)
    (hKkern_in : Kkern ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) α))
    (hfactor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ Kkern → factor y = 0) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => Set.indicator Kkern coef y * factor y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_bare : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y) Ω :=
    memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
      hKkern_compact hKkern_in hcoef_chart hfactor_memWkp hfactor_ae_zero
  have h_ae : (fun y => Set.indicator Kkern coef y * factor y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => coef y * factor y) := by
    have hfactor_ae_zero' : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
        y ∉ Kkern → factor y = 0 := by
      have h := hfactor_ae_zero
      rw [chartL2Measure] at h
      exact h
    filter_upwards [hfactor_ae_zero'] with y hy
    by_cases hyK : y ∈ Kkern
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK, zero_mul, hy hyK, mul_zero]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr h_bare

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma memWkp_offKernelSmoothCoef_mul
    (α : M) (K : ℕ)
    {coef factor : EuclN → ℝ}
    {Kkern : Set EuclN}
    (hKkern_compact : IsCompact Kkern)
    (hKkern_in : Kkern ⊆ chartTargetEuclid (I := I) (M := M) α)
    (hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞) coef
      (chartTargetEuclid (I := I) (M := M) α))
    (hcoef_zero_off : ∀ y : EuclN, y ∉ Kkern → coef y = 0)
    (hfactor_memWkp : MemWkp (d := Module.finrank ℝ E) K 2 factor
      (chartTargetEuclid (I := I) (M := M) α)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => coef y * factor y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_supp : Function.support coef ⊆ Kkern := by
    intro z hz
    by_contra hzk
    exact hz (hcoef_zero_off z hzk)
  have h_tsupp : tsupport coef ⊆ Kkern :=
    closure_minimal h_supp hKkern_compact.isClosed
  have h_tsupp_Ω : tsupport coef ⊆ Ω := h_tsupp.trans hKkern_in
  have hcoef_smooth : ContDiff ℝ (⊤ : ℕ∞) coef := by
    have h_open_compl : IsOpen ((tsupport coef)ᶜ) :=
      (isClosed_tsupport _).isOpen_compl
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy_supp : y ∈ tsupport coef
    · have hy_chart : y ∈ Ω := h_tsupp_Ω hy_supp
      exact (hcoef_chart y hy_chart).contDiffAt (hΩ_open.mem_nhds hy_chart)
    · have h_eq_zero : coef =ᶠ[𝓝 y] (fun _ : EuclN => (0 : ℝ)) := by
        filter_upwards [h_open_compl.mem_nhds hy_supp] with z hz
        exact image_eq_zero_of_notMem_tsupport hz
      exact contDiffAt_const.congr_of_eventuallyEq h_eq_zero
  have hcoef_cs : HasCompactSupport coef :=
    HasCompactSupport.of_support_subset_isCompact hKkern_compact h_supp
  obtain ⟨C, _hC_nn, hC_bd⟩ :=
    exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
      (d := Module.finrank ℝ E) hcoef_smooth hcoef_cs K
  exact MemWkp.smul_smooth_bounded (d := Module.finrank ℝ E) K
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open hcoef_smooth
    (fun j _hj y _hy => hC_bd y j _hj) hfactor_memWkp

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma recipDensityOnEuclid_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => 1 / Laplacian.MetricExtension.densityOnEuclid (I := I) g α y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  contDiffOn_const.div
    (Laplacian.MetricExtension.densityOnEuclid_contDiffOn (I := I) g α)
    (fun _ hy =>
      (Laplacian.MetricExtension.densityOnEuclid_pos (I := I) g α hy).ne')

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma eigenvectorVec_pou_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
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
    h_pou β Q
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
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorChartRHS_summand1_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (eigenvectorVec_pou_memWkp (I := I) (M := M) g r s i (K + 1)
    h_pou α P₀).le_of_le (Nat.le_succ K)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem crossLeftLimitComponent_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r (s + 1)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((crossLeftLimitComponent (I := I) (M := M)
          g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  rw [crossLeftLimitComponent]
  exact tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r (s + 1)
    (tensorCovGradL2Compl (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s i)) α P K
    (fun β Q => eigenvectorCovGrad_pou_memWkp (I := I) (M := M)
      g r s i K h_pou β Q)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem crossRightLimitComponent_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((crossRightLimitComponent (I := I) (M := M)
          g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  rw [crossRightLimitComponent]
  exact tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r s
    (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
      (eigenvectorResolvent (I := I) (M := M) g r s i)) α P K
    (fun β Q => (h_pou β Q).le_of_le (Nat.le_succ K))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
lemma componentLpLimit_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((componentLpLimit (I := I) (M := M) g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_comp : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartRHS_summand1_memWkp (I := I) (M := M)
      g r s i α P K h_pou
  have h_ae : (fun y => ((componentLpLimit (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul i.fst.val
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          i) α P)
    have h_smul' : (fun y => ((componentLpLimit (I := I) (M := M)
          g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        (fun y => i.fst.val •
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
              i) α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
      rw [componentLpLimit]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_comp i.fst.val)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma componentLpLimit_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((componentLpLimit (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  have h_smul : (fun y => ((componentLpLimit (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    rw [componentLpLimit]
    exact Lp.coeFn_smul i.fst.val _
  have h_comp_zero := tensorL2ChartComponent_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
    α P
  filter_upwards [h_smul, h_comp_zero] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
lemma partialLpLimit_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((partialLpLimit (I := I) (M := M) g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_comp_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorVec_pou_memWkp (I := I) (M := M) g r s i (K + 1)
      h_pou α P
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i α P k)
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartWeakPartial_hasWeakPartialDeriv (I := I) (M := M)
      g r s i α P k
  have h_weak_memLp : MemLp
      (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i α P k) 2
      ((volume : Measure EuclN).restrict Ω) := by
    rw [eigenvectorChartWeakPartial]
    exact Lp.memLp _
  have h_weak_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i α P k)
      Ω :=
    memWkp_of_weakPartial_of_memWkp_succ hΩ_open k
      h_weak_memLp h_weak h_comp_succ
  have h_ae : (fun y => ((partialLpLimit (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i α P k y) := by
    have h_smul := Lp.coeFn_smul i.fst.val
      (eigenvectorChartPartialLp (I := I) (M := M) g r s i α P k)
    have h_smul' : (fun y => ((partialLpLimit (I := I) (M := M)
          g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        (fun y => i.fst.val •
          eigenvectorChartWeakPartial (I := I) (M := M)
            g r s i α P k y) := by
      rw [partialLpLimit, eigenvectorChartWeakPartial]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_weak_memWkp i.fst.val)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
private lemma partialLpLimit_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        ((partialLpLimit (I := I) (M := M) g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_comp_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    (eigenvectorVec_pou_memWkp (I := I) (M := M) g r s i (K + 1)
      h_pou α P).memW1p
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i α P k)
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartWeakPartial_hasWeakPartialDeriv (I := I) (M := M)
      g r s i α P k
  have h_weak_memLp : MemLp
      (eigenvectorChartWeakPartial (I := I) (M := M)
        g r s i α P k) 2
      ((volume : Measure EuclN).restrict Ω) := by
    rw [eigenvectorChartWeakPartial]
    exact Lp.memLp _
  have h_comp_zero := tensorL2ChartComponent_ae_zero_off_chartPouKernel
    (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
    α P
  have h_weak_zero : ∀ᵐ y ∂((volume : Measure EuclN).restrict Ω),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i α P k y = 0 :=
    hasWeakPartialDeriv_ae_zero_off_of_ae_zero_off hΩ_open k
      (chartPouKernel_isCompact (I := I) (M := M) α).isClosed
      h_weak_memLp h_weak h_comp_w1p
      (by rw [← chartL2Measure]; exact h_comp_zero)
  have h_smul : (fun y => ((partialLpLimit (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i α P k y) := by
    rw [partialLpLimit, eigenvectorChartWeakPartial]
    exact Lp.coeFn_smul i.fst.val _
  have h_weak_zero' : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s i α P k y = 0 := by
    rw [chartL2Measure]; exact h_weak_zero
  filter_upwards [h_smul, h_weak_zero'] with y hy hy_zero hyK
  rw [hy, smul_eq_mul, hy_zero hyK, mul_zero]

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem cutoffPartialLpLimit_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_pou_eigen : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
              i) β Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) :=
    fun β Q => eigenvectorVec_pou_memWkp (I := I) (M := M)
      g r s i (K + 1) h_pou β Q
  have h_cutoff_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i)
      α P (K + 1) h_pou_eigen
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv
      (I := I) (M := M) g r s i α P k
  have h_weak_memLp : MemLp
      ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
      ((volume : Measure EuclN).restrict Ω) := Lp.memLp _
  have h_weak_memWkp : MemWkp (d := Module.finrank ℝ E) K 2
      ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) Ω :=
    memWkp_of_weakPartial_of_memWkp_succ hΩ_open k
      h_weak_memLp h_weak h_cutoff_succ
  have h_ae : (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul i.fst.val
      (eigenvectorCutoffChartPartialLp (I := I) (M := M)
        g r s i α P k)
    have h_smul' : (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
          g r s i α P k :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        (fun y => i.fst.val •
          ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
            g r s i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
      rw [cutoffPartialLpLimit]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_weak_memWkp i.fst.val)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem weightedGradCoeffDivLimit_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (l : Fin (Module.finrank ℝ E)) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (weightedGradCoeffDivLimit (I := I) (M := M) g r s i α P₀ l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  unfold weightedGradCoeffDivLimit
  refine MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open ?_ ?_
  · have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s)
        (k : Fin (Module.finrank ℝ E)) (p : TensorCompIdx (E := E) r s),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (euclidPartial (E := E) l
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)) y *
            ((componentLpLimit (I := I) (M := M) g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      fun P Q k p => memWkp_indicatorSmoothCoef_mul_aeZeroFactor
        (I := I) (M := M) α K
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
        (euclidPartial_weightedGradFactor_contDiffOn (I := I) (M := M)
          g r s α P₀ l P Q k p)
        (componentLpLimit_memWkp (I := I) (M := M)
          g r s i α p K h_pou)
        (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
          g r s i α p)
    exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), ∑ p : TensorCompIdx (E := E) r s,
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (euclidPartial (E := E) l
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p)) y *
            ((componentLpLimit (I := I) (M := M) g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
        hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q y => ∑ k : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (weightedGradFactor (I := I) (M := M)
                    g r s α P₀ l P Q k p)) y *
              ((componentLpLimit (I := I) (M := M) g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun Q _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k y => ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (weightedGradFactor (I := I) (M := M)
                    g r s α P₀ l P Q k p)) y *
              ((componentLpLimit (I := I) (M := M) g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun k _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (weightedGradFactor (I := I) (M := M)
                    g r s α P₀ l P Q k p)) y *
              ((componentLpLimit (I := I) (M := M) g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun p _ => h_leaf P Q k p))))
  · have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s)
        (k : Fin (Module.finrank ℝ E)) (p : TensorCompIdx (E := E) r s),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
            ((partialLpLimit (I := I) (M := M) g r s i α p l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      fun P Q k p => memWkp_indicatorSmoothCoef_mul_aeZeroFactor
        (I := I) (M := M) α K
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
        (weightedGradFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q k p)
        (partialLpLimit_memWkp (I := I) (M := M)
          g r s i α p l K h_pou)
        (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
          g r s i α p l K h_pou)
    exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), ∑ p : TensorCompIdx (E := E) r s,
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
            ((partialLpLimit (I := I) (M := M) g r s i α p l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
        hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q y => ∑ k : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
              ((partialLpLimit (I := I) (M := M) g r s i α p l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun Q _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k y => ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
              ((partialLpLimit (I := I) (M := M) g r s i α p l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun k _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun p y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (weightedGradFactor (I := I) (M := M) g r s α P₀ l P Q k p) y *
              ((partialLpLimit (I := I) (M := M) g r s i α p l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun p _ => h_leaf P Q k p))))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorChartRHS_summand2_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r (s + 1)),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
            crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossLeftLimitComponent (I := I) (M := M) g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω := by
    intro P Q
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossLeftLimitComponent (I := I) (M := M)
            g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossLeftLimitComponent_memWkp (I := I) (M := M)
        g r s i α P K h_pou
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r (s + 1) α P Q).mul
        (crossLeftTestCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q)
    have h_factor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossLeftLimitComponent (I := I) (M := M) g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossLeftLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r (s + 1)
        (tensorCovGradL2Compl (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α P
    exact memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      hcoef_chart h_factor h_factor_ae_zero
  exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
    (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
    (fun P y => ∑ Q : TensorCompIdx (E := E) r (s + 1),
      (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r (s + 1)))
      (fun Q y => (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
          crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossLeftLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun Q _ => h_leaf P Q))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorChartRHS_summand3_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
            crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
          ((crossRightLimitComponent (I := I) (M := M) g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω := by
    intro P Q
    have h_factor : MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => ((crossRightLimitComponent (I := I) (M := M)
            g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      crossRightLimitComponent_memWkp (I := I) (M := M)
        g r s i α P K h_pou
    have hcoef_chart : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun y => covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) Ω :=
      (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).mul
        (crossRightTestValueCoeff_contDiffOn (I := I) (M := M) g r s α P₀ Q)
    have h_factor_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
        y ∉ cutoffChartKernelEuclid (I := I) (M := M) α →
          ((crossRightLimitComponent (I := I) (M := M) g r s i α P :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = 0 := by
      rw [crossRightLimitComponent]
      exact tensorL2ChartComponentCutoff_ae_zero_off_cutoffChartKernelEuclid
        (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s i)) α P
    exact memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
      (cutoffChartKernelEuclid_isCompact (I := I) (M := M) α)
      (cutoffChartKernelEuclid_subset_chartTargetEuclid (I := I) (M := M) α)
      hcoef_chart h_factor h_factor_ae_zero
  exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
      (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q y => (covChartMetricGram (I := I) (M := M) g r s α P Q y *
          crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
        ((crossRightLimitComponent (I := I) (M := M) g r s i α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun Q _ => h_leaf P Q))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorChartRHS_summand4_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  unfold covPrincipalRotationCoeffLimit
  have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s)
      (k l : Fin (Module.finrank ℝ E)),
      MemWkp (d := Module.finrank ℝ E) K 2
        (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
            (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
          ((partialLpLimit (I := I) (M := M) g r s i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω := by
    intro P Q k l
    exact memWkp_indicatorSmoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
      (chartPouKernel_isCompact (I := I) (M := M) α)
      (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
      (principalRotationFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
      (partialLpLimit_memWkp (I := I) (M := M) g r s i α P k K h_pou)
      (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
        g r s i α P k K h_pou)
  exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        Set.indicator (chartPouKernel (I := I) (M := M) α)
            (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
          ((partialLpLimit (I := I) (M := M) g r s i α P k :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
    (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun Q y => ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
            ((partialLpLimit (I := I) (M := M) g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun Q _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
        hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun k y => ∑ l : Fin (Module.finrank ℝ E),
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M)
                g r s α P₀ P Q k l) y *
            ((partialLpLimit (I := I) (M := M) g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun k _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun l y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (principalRotationFactor (I := I) (M := M)
                g r s α P₀ P Q k l) y *
            ((partialLpLimit (I := I) (M := M) g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun l _ => h_leaf P Q k l))))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorChartRHS_summand5_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  unfold covLowerOrderRotationValueCoeffLimit
  refine MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open ?_ ?_
  · have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s)
        (k l : Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
            ((partialLpLimit (I := I) (M := M) g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      fun P Q k l => memWkp_indicatorSmoothCoef_mul_aeZeroFactor
        (I := I) (M := M) α K
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
        (valuePartialFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l)
        (partialLpLimit_memWkp (I := I) (M := M)
          g r s i α P k K h_pou)
        (partialLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
          g r s i α P k K h_pou)
    exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
            ((partialLpLimit (I := I) (M := M) g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
        hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q y => ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
              ((partialLpLimit (I := I) (M := M) g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun Q _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k y => ∑ l : Fin (Module.finrank ℝ E),
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
              ((partialLpLimit (I := I) (M := M) g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun k _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valuePartialFactor (I := I) (M := M) g r s α P₀ P Q k l) y *
              ((partialLpLimit (I := I) (M := M) g r s i α P k :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun l _ => h_leaf P Q k l))))
  · have h_leaf : ∀ (P Q : TensorCompIdx (E := E) r s)
        (k l : Fin (Module.finrank ℝ E)) (p : TensorCompIdx (E := E) r s),
        MemWkp (d := Module.finrank ℝ E) K 2
          (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (valueComponentFactor (I := I) (M := M) g r s α P₀ P Q k l p) y *
            ((componentLpLimit (I := I) (M := M) g r s i α p :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
      fun P Q k l p => memWkp_indicatorSmoothCoef_mul_aeZeroFactor
        (I := I) (M := M) α K
        (chartPouKernel_isCompact (I := I) (M := M) α)
        (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
        (valueComponentFactor_contDiffOn (I := I) (M := M) g r s α P₀ P Q k l p)
        (componentLpLimit_memWkp (I := I) (M := M)
          g r s i α p K h_pou)
        (componentLpLimit_ae_zero_off_chartPouKernel (I := I) (M := M)
          g r s i α p)
    exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (TensorCompIdx (E := E) r s))
      (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
        ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
          ∑ p : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (valueComponentFactor (I := I) (M := M)
                  g r s α P₀ P Q k l p) y *
              ((componentLpLimit (I := I) (M := M) g r s i α p :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
        hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
        (fun Q y => ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valueComponentFactor (I := I) (M := M)
                    g r s α P₀ P Q k l p) y *
                ((componentLpLimit (I := I) (M := M) g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun Q _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
          (fun k y => ∑ l : Fin (Module.finrank ℝ E),
            ∑ p : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valueComponentFactor (I := I) (M := M)
                    g r s α P₀ P Q k l p) y *
                ((componentLpLimit (I := I) (M := M) g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun k _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
            (fun l y => ∑ p : TensorCompIdx (E := E) r s,
              Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valueComponentFactor (I := I) (M := M)
                    g r s α P₀ P Q k l p) y *
                ((componentLpLimit (I := I) (M := M) g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun l _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
              hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
              (fun p y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                  (valueComponentFactor (I := I) (M := M)
                    g r s α P₀ P Q k l p) y *
                ((componentLpLimit (I := I) (M := M) g r s i α p :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              (fun p _ => h_leaf P Q k l p)))))

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorChartRHS_summand6_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (1 / Laplacian.MetricExtension.densityOnEuclid (I := I) g α y) *
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_sum : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        weightedGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ l y) Ω :=
    memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
      (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun l y => weightedGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀ l y)
      (fun l _ => weightedGradCoeffDivLimit_memWkp (I := I) (M := M)
        g r s i α P₀ l K h_pou)
  have h_sum_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y) = 0 :=
    Filter.Eventually.of_forall (fun y hy_imp => Finset.sum_eq_zero
      (fun l _ => weightedGradCoeffDivLimit_eq_zero_off_chartPouKernel_unconditional
        (I := I) (M := M) g r s i α P₀ l hy_imp))
  exact memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (recipDensityOnEuclid_contDiffOn (I := I) (M := M) g α)
    h_sum h_sum_ae_zero

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorChartRHS_summand7_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (1 / Laplacian.MetricExtension.densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h_div : MemWkp (d := Module.finrank ℝ E) K 2
      (crossRightGradCoeffDivLimit (I := I) (M := M)
        g r s i α P₀) Ω := by
    unfold crossRightGradCoeffDivLimit
    refine MemWkp.add (d := Module.finrank ℝ E) (by norm_num) hΩ_open ?_ ?_
    · have h_leaf : ∀ (l : Fin (Module.finrank ℝ E))
          (P Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q)) y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            Ω := by
        intro l P Q
        have h_indic : (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (euclidPartial (E := E) l
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q)) y *
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) =
            (fun y => euclidPartial (E := E) l
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
          funext y
          by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
          · rw [Set.indicator_of_mem hyK]
          · rw [Set.indicator_of_notMem hyK,
              euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
                (I := I) (M := M) g r s α P₀ l P Q hyK]
        rw [h_indic]
        exact memWkp_offKernelSmoothCoef_mul (I := I) (M := M) α K
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
          (euclidPartial_crossRightDivFactor_contDiffOn (I := I) (M := M)
            g r s α P₀ l P Q)
          (fun y hy => euclidPartial_crossRightDivFactor_eq_zero_off_chartPouKernel
            (I := I) (M := M) g r s α P₀ l P Q hy)
          (crossRightLimitComponent_memWkp (I := I) (M := M)
            g r s i α P K h_pou)
      exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q)) y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun l _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q)) y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun Q y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (euclidPartial (E := E) l
                  (crossRightDivFactor (I := I) (M := M)
                    g r s α P₀ l P Q)) y *
              ((crossRightLimitComponent (I := I) (M := M)
                g r s i α P :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun Q _ => h_leaf l P Q)))
    · have h_leaf : ∀ (l : Fin (Module.finrank ℝ E))
          (P Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) K 2
            (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            Ω := by
        intro l P Q
        have h_indic : (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
              (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
            ((cutoffPartialLpLimit (I := I) (M := M)
              g r s i α P l :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) =
            (fun y => crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q y *
              ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
          funext y
          by_cases hyK : y ∈ chartPouKernel (I := I) (M := M) α
          · rw [Set.indicator_of_mem hyK]
          · rw [Set.indicator_of_notMem hyK,
              crossRightDivFactor_eq_zero_off_chartPouKernel
                (I := I) (M := M) g r s α P₀ l P Q hyK]
        rw [h_indic]
        exact memWkp_offKernelSmoothCoef_mul (I := I) (M := M) α K
          (chartPouKernel_isCompact (I := I) (M := M) α)
          (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
          (crossRightDivFactor_contDiffOn (I := I) (M := M) g r s α P₀ l P Q)
          (fun y hy => crossRightDivFactor_eq_zero_off_chartPouKernel
            (I := I) (M := M) g r s α P₀ l P Q hy)
          (cutoffPartialLpLimit_memWkp (I := I) (M := M)
            g r s i α P l K h_pou)
      exact memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num) hΩ_open
        (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
        (fun l y => ∑ P : TensorCompIdx (E := E) r s,
          ∑ Q : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        (fun l _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
          hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
          (fun P y => ∑ Q : TensorCompIdx (E := E) r s,
            Set.indicator (chartPouKernel (I := I) (M := M) α)
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (fun P _ => memWkp_finsetSum (d := Module.finrank ℝ E) (by norm_num)
            hΩ_open (Finset.univ : Finset (TensorCompIdx (E := E) r s))
            (fun Q y => Set.indicator (chartPouKernel (I := I) (M := M) α)
                (crossRightDivFactor (I := I) (M := M) g r s α P₀ l P Q) y *
              ((cutoffPartialLpLimit (I := I) (M := M)
                g r s i α P l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (fun Q _ => h_leaf l P Q)))
  have h_div_ae_zero : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      y ∉ chartPouKernel (I := I) (M := M) α →
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y = 0 :=
    Filter.Eventually.of_forall (fun y hy_imp =>
      crossRightGradCoeffDivLimit_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ hy_imp)
  exact memWkp_smoothCoef_mul_aeZeroFactor (I := I) (M := M) α K
    (chartPouKernel_isCompact (I := I) (M := M) α)
    (chartPouKernel_subset_chartTargetEuclid (I := I) (M := M) α)
    (recipDensityOnEuclid_contDiffOn (I := I) (M := M) g α)
    h_div h_div_ae_zero

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in

omit [CompleteSpace E] in
theorem eigenvectorChartRHS_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (K + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartRHS (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have h1 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
            i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartRHS_summand1_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
  have h2 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ P : TensorCompIdx (E := E) r (s + 1),
        ∑ Q : TensorCompIdx (E := E) r (s + 1),
          (covChartMetricGram (I := I) (M := M) g r (s + 1) α P Q y *
              crossLeftTestCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossLeftLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartRHS_summand2_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
  have h3 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => ∑ P : TensorCompIdx (E := E) r s,
        ∑ Q : TensorCompIdx (E := E) r s,
          (covChartMetricGram (I := I) (M := M) g r s α P Q y *
              crossRightTestValueCoeff (I := I) (M := M) g r s α P₀ Q y) *
            ((crossRightLimitComponent (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorChartRHS_summand3_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
  have h4 : MemWkp (d := Module.finrank ℝ E) K 2
      (covPrincipalRotationCoeffLimit (I := I) (M := M)
        g r s i α P₀) Ω :=
    eigenvectorChartRHS_summand4_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
  have h5 : MemWkp (d := Module.finrank ℝ E) K 2
      (covLowerOrderRotationValueCoeffLimit (I := I) (M := M)
        g r s i α P₀) Ω :=
    eigenvectorChartRHS_summand5_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
  have h6 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (1 / Laplacian.MetricExtension.densityOnEuclid (I := I) g α y) *
        (∑ l : Fin (Module.finrank ℝ E),
          weightedGradCoeffDivLimit (I := I) (M := M)
            g r s i α P₀ l y)) Ω :=
    eigenvectorChartRHS_summand6_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
  have h7 : MemWkp (d := Module.finrank ℝ E) K 2
      (fun y => (1 / Laplacian.MetricExtension.densityOnEuclid (I := I) g α y) *
        crossRightGradCoeffDivLimit (I := I) (M := M)
          g r s i α P₀ y) Ω :=
    eigenvectorChartRHS_summand7_memWkp (I := I) (M := M)
      g r s i α P₀ K h_pou
  have h12 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp hΩ_open h1 h2
  have h123 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.add (d := Module.finrank ℝ E) hp hΩ_open h12 h3
  have h1234 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp hΩ_open h123 h4
  have h12345 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp hΩ_open h1234 h5
  have h123456 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.add (d := Module.finrank ℝ E) hp hΩ_open h12345 h6
  have h1234567 : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.sub (d := Module.finrank ℝ E) hp hΩ_open h123456 h7
  have h_assembled : MemWkp (d := Module.finrank ℝ E) K 2 _ Ω :=
    MemWkp.const_smul (d := Module.finrank ℝ E) hp hΩ_open h1234567 (i.fst.val)⁻¹
  refine (MemWkp_congr_ae (d := Module.finrank ℝ E) hp hΩ_open
    (Filter.Eventually.of_forall (fun y => ?_))).mp h_assembled
  rw [eigenvectorChartRHS]

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
