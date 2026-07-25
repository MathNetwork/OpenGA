import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.MixedPartials
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.VariationalIdentity.LeibnizCoefficients
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.DerivedDataConstructor
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.VariationalIdentity
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.ChosenFChartDerivMemW1p
import DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.BaseFChart.MemWkpTwoTwo
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.FChartEffDef
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.TwiceDifferentiated.FChartEffDef
import DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.ChartData
import DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplViaH3


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedDifferentiatedData

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
open DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1Compl
open DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3
open DifferentialGeometry.Analysis.Laplacian.DerivedChartBilinearH1ComplDataCanonical
open DifferentialGeometry.Analysis.Laplacian.TwiceDifferentiatedVariationalIdentity
open DifferentialGeometry.Analysis.Laplacian.ChosenFChartDerivMemW1p
open DifferentialGeometry.Analysis.Laplacian.BaseFChartMemW22
open DifferentialGeometry.Analysis.Laplacian.FChartEffDef
open DifferentialGeometry.Analysis.Laplacian.FChartEffTwiceDef
open DifferentialGeometry.Analysis.Laplacian.ChosenThirdMixedPartialChartPushed
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

structure IteratedDiffChartBilinearData
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) (m : ℕ) where

  directions : Fin m → Fin (Module.finrank ℝ E)

  diffChartForcing : EuclN → ℝ

  fChartEff_memLp_weighted :
    MemLp diffChartForcing 2
      ((chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α))

  m_diff_variational_identity :
    ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            weightedInvGramOnEuclid (I := I) g α i j y *
              chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                (m + 1) (Fin.cons i directions) y *
              (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
        ∂(volume : Measure EuclN)) +
      (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
            m directions y * ψ y
        ∂(volume : Measure EuclN)) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y * diffChartForcing y * ψ y
        ∂(volume : Measure EuclN)

def IteratedDiffChartBilinearData.mk_from_hypotheses
    {g : SmoothRiemannianMetric I M} {α : M}
    {u_h : H1Compl (I := I) (M := M) g} {m : ℕ}
    (directions : Fin m → Fin (Module.finrank ℝ E))
    (diffChartForcing : EuclN → ℝ)
    (fChartEff_memLp_weighted :
      MemLp diffChartForcing 2
        ((chartPulledWeightedMeasure (I := I) g α).restrict
          (chartTargetEuclid (I := I) (M := M) α)))
    (m_diff_variational_identity :
      ∀ ψ : EuclN → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ chartTargetEuclid (I := I) (M := M) α →
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
                  (m + 1) (Fin.cons i directions) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN)) +
        (∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h
              m directions y * ψ y
          ∂(volume : Measure EuclN)) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y * diffChartForcing y * ψ y
          ∂(volume : Measure EuclN)) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h m :=
  { directions := directions
    diffChartForcing := diffChartForcing
    fChartEff_memLp_weighted := fChartEff_memLp_weighted
    m_diff_variational_identity := m_diff_variational_identity }

namespace IteratedDiffChartBilinearData

omit [NeZero (Module.finrank ℝ E)] in
private lemma m_zero_principal_integrand_eq
    {g : SmoothRiemannianMetric I M} {α : M}
    {u_h : H1Compl (I := I) (M := M) g}
    (y : EuclN) (i j : Fin (Module.finrank ℝ E)) :
    weightedInvGramOnEuclid (I := I) g α i j y *
        chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 1
          (Fin.cons i (Fin.elim0)) y *
        (fderiv ℝ (fun _ : EuclN => (0 : ℝ)) y) (EuclideanSpace.single j 1) =
      weightedInvGramOnEuclid (I := I) g α i j y *
        chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i y *
        (fderiv ℝ (fun _ : EuclN => (0 : ℝ)) y) (EuclideanSpace.single j 1) := by
  rw [chosenMthMixedPartialChartPushedU_one_eq_chosenFirstPartial]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenMthMixed_one_cons_eq_chartPushedChosenFirstPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (i : Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 1
        (Fin.cons i (Fin.elim0)) =
      chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i := by
  rw [chosenMthMixedPartialChartPushedU_one_eq_chosenFirstPartial]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenMthMixed_zero_elim0_eq_chartPushed
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 0
        (Fin.elim0) =
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) := rfl

private lemma base_u_chart_ae_eq_chartPushed
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        hu_h).u_chart =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h) : M → ℝ) := by
  classical
  have h_coeFn :=
    DifferentialGeometry.Analysis.Laplacian.LaplacianDomainVariationalIdentityIntegralForm.chartPushedLpFromLp_coeFn
      (I := I) (M := M) g α (H1ComplToLp (I := I) (M := M) g u_h)
  have h_meas : MeasurableSet
      (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have h_v_abs_w :
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) ≪
      (chartPulledWeightedMeasure (I := I) g α).restrict
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro A hA
    unfold chartPulledWeightedMeasure at hA
    rw [show ((volume : Measure EuclN).withDensity
        (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))).restrict
        (chartTargetEuclid (I := I) (M := M) α) =
        ((volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α)).withDensity
          (fun y => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      from MeasureTheory.restrict_withDensity h_meas _] at hA
    rw [MeasureTheory.withDensity_apply_eq_zero'
      (μ := (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α))
      (f := fun y : EuclN => ENNReal.ofReal (densityOnEuclid (I := I) g α y))
      (ENNReal.measurable_ofReal.comp_aemeasurable
        ((densityOnEuclid_continuousOn (I := I) g α).aemeasurable h_meas))] at hA
    rw [Measure.restrict_apply' h_meas]
    rw [Measure.restrict_apply' h_meas] at hA
    refine MeasureTheory.measure_mono_null ?_ hA
    intro y ⟨hy_A, hy_chart⟩
    refine ⟨⟨?_, hy_A⟩, hy_chart⟩
    have h_pos : 0 < densityOnEuclid (I := I) g α y :=
      densityOnEuclid_pos (I := I) g α hy_chart
    exact (ENNReal.ofReal_pos.mpr h_pos).ne'
  exact h_v_abs_w.ae_le h_coeFn

private lemma base_weak_partial_ae_eq_chartPushedChosenFirstPartial_aux
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (i : Fin (Module.finrank ℝ E)) :
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).weak_partial i =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i :=
  DifferentialGeometry.Analysis.Laplacian.DiffChartBilinearH1ComplH3.chartPushedWeakPartialLp_ae_eq_chosenFirstPartial_on_chartTarget
    (I := I) (M := M) g α hu_h i

def ofBase
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h 0 where
  directions := Fin.elim0
  diffChartForcing :=
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h)).f_chart
  fChartEff_memLp_weighted :=
    (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
      (laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h)).f_chart_memLp_weighted
  m_diff_variational_identity := by
    classical
    intro ψ hψ_smooth hψ_cs hψ_supp
    set hu_h_lap : u_h ∈ laplacianDomain (I := I) (M := M) g :=
      laplacianDomainPow_succ_subset_laplacianDomain
        (I := I) (M := M) g 1 hu_h
    set D := chartBilinearH1ComplData_of_laplacianDomain
      (I := I) (M := M) g α hu_h_lap with hD_def
    have h_base := D.variational_identity ψ hψ_smooth hψ_cs hψ_supp
    have h_wp_ae := base_weak_partial_ae_eq_chartPushedChosenFirstPartial_aux
      (I := I) (M := M) g α hu_h
    have h_u_ae := base_u_chart_ae_eq_chartPushed
      (I := I) (M := M) g α hu_h_lap
    have h_principal_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 1
                  (Fin.cons i (Fin.elim0)) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                D.weak_partial i y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) := by
      refine MeasureTheory.integral_congr_ae ?_
      have h_wp_all : ∀ i, (chartBilinearH1ComplData_of_laplacianDomain
            (I := I) (M := M) g α hu_h_lap).weak_partial i =ᵐ[
            (volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)]
          chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i :=
        fun i => base_weak_partial_ae_eq_chartPushedChosenFirstPartial_aux
          (I := I) (M := M) g α hu_h i
      have h_ae_eqs : ∀ i,
          ∀ᵐ y ∂((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)),
            chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i y =
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M)
              g α hu_h_lap).weak_partial i y := by
        intro i
        filter_upwards [h_wp_all i] with y hy
        exact hy.symm
      have h_all_ae :
          ∀ᵐ y ∂((volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α)),
            ∀ i : Fin (Module.finrank ℝ E),
              chartPushedChosenFirstPartial (I := I) (M := M) g α u_h i y =
              (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M)
                g α hu_h_lap).weak_partial i y := by
        rw [Filter.eventually_all]
        exact h_ae_eqs
      filter_upwards [h_all_ae] with y hy
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [chosenMthMixed_one_cons_eq_chartPushedChosenFirstPartial
        (I := I) (M := M) g α u_h i, hy i]
    have h_mass_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 0
              (Fin.elim0) y * ψ y
          ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            D.u_chart y * ψ y
          ∂(volume : Measure EuclN) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_u_ae] with y hy
      rw [chosenMthMixed_zero_elim0_eq_chartPushed]
      rw [hy]
    rw [h_principal_eq, h_mass_eq]
    exact h_base

end IteratedDiffChartBilinearData

namespace IteratedDiffChartBilinearData

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenMthMixed_two_cons_const_eq_chosenSecond
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (i l : Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 2
        (Fin.cons i (fun _ : Fin 1 => l)) =
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l := by
  apply chosenMthMixedPartialChartPushedU_two_eq_chosenSecondPartialChartPushedU
  · rfl
  · rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenMthMixed_one_const_eq_chartPushedChosenFirstPartial
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (l : Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 1
        (fun _ : Fin 1 => l) =
      chartPushedChosenFirstPartial (I := I) (M := M) g α u_h l := by
  rw [chosenMthMixedPartialChartPushedU_one_eq_chosenFirstPartial]

def ofDiff
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l : Fin (Module.finrank ℝ E)) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h 1 where
  directions := fun _ => l
  diffChartForcing :=
    DifferentialGeometry.Analysis.Laplacian.FChartEffDef.diffChartForcing
      (I := I) (M := M) g α l hu_h
  fChartEff_memLp_weighted :=
    DifferentialGeometry.Analysis.Laplacian.FChartEffDef.diffChartForcing_memLp_two_weighted
      (I := I) (M := M) (g := g) (α := α) (l := l) (hu_h := hu_h)
  m_diff_variational_identity := by
    classical
    intro ψ hψ_smooth hψ_cs hψ_supp
    have h_once := derived_variational_identity_holds
      (I := I) (M := M) g α l hu_h hψ_smooth hψ_cs hψ_supp
    have h_principal_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 2
                  (Fin.cons i (fun _ : Fin 1 => l)) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h i l y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) := by
      refine MeasureTheory.setIntegral_congr_fun
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet ?_
      intro y _hy
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [chosenMthMixed_two_cons_const_eq_chosenSecond
        (I := I) (M := M) g α u_h i l]
    have h_wp_ae :=
      base_weak_partial_ae_eq_chartPushedChosenFirstPartial_aux
        (I := I) (M := M) g α hu_h l
    have h_mass_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 1
              (fun _ : Fin 1 => l) y * ψ y
          ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            (chartBilinearH1ComplData_of_laplacianDomain (I := I) (M := M) g α
              (laplacianDomainPow_succ_subset_laplacianDomain
                (I := I) (M := M) g 1 hu_h)).weak_partial l y * ψ y
          ∂(volume : Measure EuclN) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [h_wp_ae] with y hy
      rw [chosenMthMixed_one_const_eq_chartPushedChosenFirstPartial
        (I := I) (M := M) g α u_h l]
      rw [← hy]
    rw [h_principal_eq, h_mass_eq]
    exact h_once

end IteratedDiffChartBilinearData

namespace IteratedDiffChartBilinearData

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenMthMixed_three_cons_two_eq_chosenThird
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (i l₁ l₂ : Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 3
        (Fin.cons i (![l₁, l₂])) =
      chosenThirdMixedPartialChartPushedU (I := I) (M := M) g α u_h i l₁ l₂ := by
  apply chosenMthMixedPartialChartPushedU_three_eq_chosenThirdMixedPartialChartPushedU
  · rfl
  · rfl
  · rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma chosenMthMixed_two_pair_eq_chosenSecond
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) :
    chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 2
        (![l₁, l₂]) =
      chosenSecondPartialChartPushedU (I := I) (M := M) g α u_h l₁ l₂ := by
  apply chosenMthMixedPartialChartPushedU_two_eq_chosenSecondPartialChartPushedU
  · rfl
  · rfl

def ofDiffTwice
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (l₁ l₂ : Fin (Module.finrank ℝ E)) :
    IteratedDiffChartBilinearData (I := I) (M := M) g α u_h 2 where
  directions := ![l₁, l₂]
  diffChartForcing :=
    DifferentialGeometry.Analysis.Laplacian.FChartEffTwiceDef.effectiveSourceChartSecondOrder
      (I := I) (M := M) g α l₁ l₂ hu_h
  fChartEff_memLp_weighted :=
    DifferentialGeometry.Analysis.Laplacian.FChartEffTwiceDef.fChartEffTwice_memLp_two_weighted
      (I := I) (M := M) (g := g) (α := α) (l₁ := l₁) (l₂ := l₂) (hu_h := hu_h)
  m_diff_variational_identity := by
    classical
    intro ψ hψ_smooth hψ_cs hψ_supp
    have h_base_f_chart_memWkp22 :=
      base_f_chart_memWkp_two_two
        (I := I) (M := M) g α hu_h
    have h_chosenFChartDeriv_memW1p :=
      chosenFChartDeriv_memW1p_truly_unconditional
        (I := I) (M := M) g α hu_h l₁ h_base_f_chart_memWkp22
    have h_twice := twice_differentiated_variational_identity_holds
      (I := I) (M := M) g α hu_h l₁ l₂ h_chosenFChartDeriv_memW1p
      hψ_smooth hψ_cs hψ_supp
    have h_principal_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 3
                  (Fin.cons i (![l₁, l₂])) y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          (∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              weightedInvGramOnEuclid (I := I) g α i j y *
                chosenThirdMixedPartialChartPushedU
                  (I := I) (M := M) g α u_h i l₁ l₂ y *
                (fderiv ℝ ψ y) (EuclideanSpace.single j 1))
          ∂(volume : Measure EuclN) := by
      refine MeasureTheory.setIntegral_congr_fun
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet ?_
      intro y _hy
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [chosenMthMixed_three_cons_two_eq_chosenThird
        (I := I) (M := M) g α u_h i l₁ l₂]
    have h_mass_eq :
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h 2
              (![l₁, l₂]) y * ψ y
          ∂(volume : Measure EuclN) =
        ∫ y in chartTargetEuclid (I := I) (M := M) α,
          densityOnEuclid (I := I) g α y *
            chosenSecondPartialChartPushedU
              (I := I) (M := M) g α u_h l₁ l₂ y * ψ y
          ∂(volume : Measure EuclN) := by
      refine MeasureTheory.setIntegral_congr_fun
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet ?_
      intro y _hy
      rw [chosenMthMixed_two_pair_eq_chosenSecond
        (I := I) (M := M) g α u_h l₁ l₂]
    rw [h_principal_eq, h_mass_eq]
    exact h_twice

end IteratedDiffChartBilinearData

end IteratedDifferentiatedData
end Laplacian
end Analysis
end DifferentialGeometry

end
