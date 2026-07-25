import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.WeakPartialOnVolume
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolev


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace DiffChartBilinearH1ComplH3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.ChartPushedWeakPartialOnVolume
open DifferentialGeometry.Analysis.Laplacian.H1ComplGradientH1LipschitzBound
open DifferentialGeometry.Analysis.Laplacian.H1ComplWeakPartialLimit
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def chartPushedChosenFirstPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
    (d := Module.finrank ℝ E) 2 i
    (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
      ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ))
    (chartTargetEuclid (I := I) (M := M) α)

theorem chartPushedChosenFirstPartial_memW1p_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i)
      (chartTargetEuclid (I := I) (M := M) α) := by
  have h_memWkp_2 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chartPushed (I := I) (M := M)
        (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_memWkpChart :=
      (DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_two_h2_plus_rhs_h2
        (I := I) (M := M) g hu_h).1.1
    exact h_memWkpChart α
  have h_step := h_memWkp_2.chosenWeakPartial_mem i
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p] at h_step
  exact h_step

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma locallyIntegrable_of_memLp_two_compact_open_subset
    (K Ω' : Set EuclN) (_hK_compact : IsCompact K) (hΩ'_subset_K : Ω' ⊆ K)
    (hΩ'_meas : MeasurableSet Ω')
    {f : EuclN → ℝ}
    (hf_memLp_K : MemLp f 2 ((volume : Measure EuclN).restrict K)) :
    LocallyIntegrable f ((volume : Measure EuclN).restrict Ω') := by
  have h_eq : ((volume : Measure EuclN).restrict K).restrict Ω' =
      (volume : Measure EuclN).restrict Ω' := by
    rw [Measure.restrict_restrict hΩ'_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hΩ'_subset_K
  have hf_memLp_Ω' : MemLp f 2 ((volume : Measure EuclN).restrict Ω') := by
    rw [← h_eq]; exact hf_memLp_K.restrict Ω'
  exact hf_memLp_Ω'.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)

theorem chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_precompact_open
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E))
    {Ω' K : Set EuclN} (hΩ'_open : IsOpen Ω') (hK_compact : IsCompact K)
    (hΩ'_subset_K : Ω' ⊆ K)
    (hK_in : K ⊆ chartTargetEuclid (I := I) (M := M) α) :
    ((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ) =ᵐ[(volume : Measure EuclN).restrict Ω']
      chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hΩ'_subset_chartTarget : Ω' ⊆ Ω := hΩ'_subset_K.trans hK_in
  set f : EuclN → ℝ := chartPushed (I := I) (M := M)
    (chartAtlasPOU I M) α
    ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) with hf_def
  have h_memWkp_2 : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2 f Ω := by
    have h_memWkpChart :=
      (DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_two_h2_plus_rhs_h2
        (I := I) (M := M) g hu_h).1.1
    exact h_memWkpChart α
  have h_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 f Ω :=
    h_memWkp_2.memW1p
  have h_chartPushed_isWeakPartial_Ω :=
    hasWeakPartialDeriv_chartPushedWeakPartialLp_on_chartTarget
      (I := I) (M := M) g α i u_h
  have h_chosenFirst_isWeakPartial_Ω :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i)
        f Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_isWeakPartial_of_mem
      h_memW1p i
  have h_chartPushed_isWeakPartial_Ω' :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
         ) : EuclN → ℝ)) f Ω' :=
    DeGiorgi.HasWeakPartialDeriv.restrict hΩ'_open hΩ'_subset_chartTarget
      h_chartPushed_isWeakPartial_Ω
  have h_chosenFirst_isWeakPartial_Ω' :
      DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) i
        (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i)
        f Ω' :=
    DeGiorgi.HasWeakPartialDeriv.restrict hΩ'_open hΩ'_subset_chartTarget
      h_chosenFirst_isWeakPartial_Ω
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hΩ'_meas : MeasurableSet Ω' := hΩ'_open.measurableSet
  have h_chartPushed_memLp_K : MemLp
      (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ)) 2 ((volume : Measure EuclN).restrict K) :=
    chartPushedWeakPartialLp_locally_memLp (I := I) (M := M) g α i u_h
      hK_compact hK_in
  have h_chosenFirst_memLp_chartTarget : MemLp
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i) 2
      ((volume : Measure EuclN).restrict Ω) :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'_memLp_of_mem
      h_memW1p i
  have h_chartTarget_restrict_K : ((volume : Measure EuclN).restrict Ω).restrict K =
      (volume : Measure EuclN).restrict K := by
    rw [Measure.restrict_restrict hK_meas]
    congr 1
    exact Set.inter_eq_self_of_subset_left hK_in
  have h_chosenFirst_memLp_K : MemLp
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i) 2
      ((volume : Measure EuclN).restrict K) := by
    rw [← h_chartTarget_restrict_K]
    exact h_chosenFirst_memLp_chartTarget.restrict K
  have h_chartPushed_locInt : LocallyIntegrable
      (((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ))
      ((volume : Measure EuclN).restrict Ω') :=
    locallyIntegrable_of_memLp_two_compact_open_subset
      K Ω' hK_compact hΩ'_subset_K hΩ'_meas h_chartPushed_memLp_K
  have h_chosenFirst_locInt : LocallyIntegrable
      (chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i)
      ((volume : Measure EuclN).restrict Ω') :=
    locallyIntegrable_of_memLp_two_compact_open_subset
      K Ω' hK_compact hΩ'_subset_K hΩ'_meas h_chosenFirst_memLp_K
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ'_open
    h_chartPushed_isWeakPartial_Ω' h_chosenFirst_isWeakPartial_Ω'
    h_chartPushed_locInt h_chosenFirst_locInt

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma chartTargetEuclid_sigmaCompact_cover
    (α : M) :
    ∃ K : ℕ → Set EuclN,
      (∀ n, IsCompact (K n)) ∧
      (∀ n, K n ⊆ chartTargetEuclid (I := I) (M := M) α) ∧
      (⋃ n, K n) = chartTargetEuclid (I := I) (M := M) α := by
  classical
  have hΩ_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  haveI : LocallyCompactSpace ↥(chartTargetEuclid (I := I) (M := M) α) :=
    hΩ_open.locallyCompactSpace
  haveI : SecondCountableTopology ↥(chartTargetEuclid (I := I) (M := M) α) :=
    inferInstance
  haveI : SigmaCompactSpace ↥(chartTargetEuclid (I := I) (M := M) α) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨K_sub, hK_sub_compact, hK_sub_cov⟩ :=
    SigmaCompactSpace.exists_compact_covering
      (X := ↥(chartTargetEuclid (I := I) (M := M) α))
  refine ⟨fun n => ((↑) : ↥(chartTargetEuclid (I := I) (M := M) α) → EuclN) '' K_sub n,
    ?_, ?_, ?_⟩
  · intro n
    exact (hK_sub_compact n).image continuous_subtype_val
  · intro n y ⟨z, _, hz_eq⟩
    rw [← hz_eq]
    exact z.2
  · apply Set.eq_of_subset_of_subset
    · rw [Set.iUnion_subset_iff]
      intro n y ⟨z, _, hz_eq⟩
      rw [← hz_eq]
      exact z.2
    · intro y hy
      let z : ↥(chartTargetEuclid (I := I) (M := M) α) := ⟨y, hy⟩
      have hz_in : z ∈ (⋃ n, K_sub n) := by rw [hK_sub_cov]; trivial
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz_in
      exact Set.mem_iUnion.mpr ⟨n, z, hn, rfl⟩

theorem chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_chartTarget
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    ((chartPushedWeakPartialLp (I := I) (M := M) g α i
        (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
       ) : EuclN → ℝ) =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨K_seq, hK_seq_compact, hK_seq_in, hK_seq_cov⟩ :=
    chartTargetEuclid_sigmaCompact_cover (I := I) (M := M) α
  have h_get_open : ∀ n, ∃ Ω_n : Set EuclN, IsOpen Ω_n ∧ K_seq n ⊆ Ω_n ∧
      ∃ K_n' : Set EuclN, IsCompact K_n' ∧ Ω_n ⊆ K_n' ∧ K_n' ⊆ Ω := by
    intro n
    obtain ⟨r, hr_pos, hr_sub⟩ :=
      (hK_seq_compact n).exists_cthickening_subset_open hΩ_open (hK_seq_in n)
    refine ⟨Metric.thickening r (K_seq n), Metric.isOpen_thickening,
      Metric.self_subset_thickening hr_pos _, Metric.cthickening r (K_seq n),
      (hK_seq_compact n).cthickening, ?_, hr_sub⟩
    exact Metric.thickening_subset_cthickening _ _
  choose Ω_seq hΩ_seq_open hK_seq_in_Ω K'_seq hK'_seq_compact hΩ_seq_in_K' hK'_in
    using h_get_open
  have h_ae_on_Ω_seq : ∀ n,
      ((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
         ) : EuclN → ℝ) =ᵐ[(volume : Measure EuclN).restrict (Ω_seq n)]
        chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i :=
    fun n => chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_precompact_open
      (I := I) (M := M) g α hu_h i (hΩ_seq_open n) (hK'_seq_compact n)
      (hΩ_seq_in_K' n) (hK'_in n)
  have h_ae_on_K_seq : ∀ n,
      ((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
         ) : EuclN → ℝ) =ᵐ[(volume : Measure EuclN).restrict (K_seq n)]
        chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i := by
    intro n
    have h_K_sub_Ω : K_seq n ⊆ Ω_seq n := hK_seq_in_Ω n
    exact (h_ae_on_Ω_seq n).filter_mono
      (MeasureTheory.ae_mono (Measure.restrict_mono h_K_sub_Ω le_rfl))
  have h_ae_union :
      ((chartPushedWeakPartialLp (I := I) (M := M) g α i
          (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α i) u_h
         ) : EuclN → ℝ) =ᵐ[(volume : Measure EuclN).restrict (⋃ n, K_seq n)]
        chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i :=
    (MeasureTheory.ae_eq_restrict_iUnion_iff K_seq _ _).mpr h_ae_on_K_seq
  rw [hK_seq_cov] at h_ae_union
  exact h_ae_union

theorem diffChartBilinearH1Compl_u_chart_deriv_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).f_chart
      (chartTargetEuclid (I := I) (M := M) α))
    (h_once_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial l₁ y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).u_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
          ∂(volume : Measure EuclN))) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
        (I := I) (M := M) g α hu_h l₁
        h_base_f_chart_memW1p h_once_identity).u_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  change DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
    (((chartPushedWeakPartialLp (I := I) (M := M) g α l₁
      (chartPushedPartialLipschitz_canonical (I := I) (M := M) g α l₁) u_h
     ) : EuclN → ℝ))
    (chartTargetEuclid (I := I) (M := M) α)
  have h_chosenFirst_memW1p :=
    chartPushedChosenFirstPartial_memW1p_two (I := I) (M := M) g α hu_h l₁
  have h_ae := chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_chartTarget
    (I := I) (M := M) g α hu_h l₁
  exact (DifferentialGeometry.Analysis.Sobolev.Euclidean.MemW1p_congr_ae
    (chartTargetEuclid_isOpen (I := I) (M := M) α) h_ae.symm).mp
    h_chosenFirst_memW1p

theorem diffChartBilinearH1Compl_f_chart_deriv_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).f_chart
      (chartTargetEuclid (I := I) (M := M) α))
    (h_once_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial l₁ y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).u_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
          ∂(volume : Measure EuclN)))
    (h_base_f_chart_memWkp22 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).f_chart
        (chartTargetEuclid (I := I) (M := M) α)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (diffChartBilinearH1ComplData_of_laplacianDomainPow_two
        (I := I) (M := M) g α hu_h l₁
        h_base_f_chart_memW1p h_once_identity).f_chart_deriv
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  change DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
    (chosenFChartDeriv (I := I) (M := M) g α hu_h l₁)
    (chartTargetEuclid (I := I) (M := M) α)
  have h_step := h_base_f_chart_memWkp22.chosenWeakPartial_mem l₁
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    at h_step
  exact h_step

theorem diffChartBilinearH1Compl_weak_partial_deriv_memW1p
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl g} (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ : Fin (Module.finrank ℝ E))
    (h_base_f_chart_memW1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).f_chart
      (chartTargetEuclid (I := I) (M := M) α))
    (h_once_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                (chosenSecondPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial l₁ y * ψ y
          ∂(volume : Measure EuclN)) =
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenFChartDeriv (I := I) (M := M) g α hu_h l₁ y * ψ y
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramDerivOnEuclid (I := I) g α i j l₁ y *
                (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
                  (laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g 1 hu_h)).weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) -
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).u_chart y * ψ y
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityDerivOnEuclid (I := I) g α l₁ y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).f_chart y * ψ y
          ∂(volume : Measure EuclN)))
    (h_chartPushed_memWkp32 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 3 2
        (chartPushed (I := I) (M := M)
          (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α))
    (i : Fin (Module.finrank ℝ E)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      ((diffChartBilinearH1ComplData_of_laplacianDomainPow_two
        (I := I) (M := M) g α hu_h l₁
        h_base_f_chart_memW1p h_once_identity).weak_partial_deriv i)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  change DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
    (chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l₁)
    (chartTargetEuclid (I := I) (M := M) α)
  have h_step_one := h_chartPushed_memWkp32.chosenWeakPartial_mem i
  have h_step_two := h_step_one.chosenWeakPartial_mem l₁
  rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
    at h_step_two
  exact h_step_two

end DiffChartBilinearH1ComplH3
end Laplacian
end Analysis
end DifferentialGeometry

end
