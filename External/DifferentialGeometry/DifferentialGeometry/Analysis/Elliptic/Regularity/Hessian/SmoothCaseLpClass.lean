import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.ChartAlphaChristoffelCorrection

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function FiberBundle
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianBridgeSmoothLp

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
open DifferentialGeometry.Analysis.Laplacian.HessianTensorChartSmooth
open DifferentialGeometry.Analysis.Laplacian.HessianChartInvariance
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaMatrix
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaFrobenius
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaLp
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge
open DifferentialGeometry.Analysis.Sobolev.Chart

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem perChartAeTransferable_smoothCase
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (α : M) :
    hessPairingMChartContribution (I := I) (M := M) g φ α
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
      =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (chartAtlasPOU I M α : M → ℝ) x *
        smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
          ((toEuclidean (E := E)) (extChartAt I α x))) := by
  classical
  have h_chart_ae := hessPairingChartLocal_smoothCase_aeEq_smoothEuclidPairing
    (I := I) (M := M) g α φ v
  set badSet : Set EuclN :=
    { y : EuclN |
        hessPairingChartLocal (I := I) (M := M) g α φ
            (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) y ≠
          smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v y } with hbadSet_def
  have h_bad_null : ((volume : Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α)) badSet = 0 := h_chart_ae
  obtain ⟨N, h_bad_sub_N, hN_meas, hN_null_restricted⟩ :=
    exists_measurable_superset_of_null h_bad_null
  have hN_null : (volume : Measure EuclN)
      (N ∩ chartTargetEuclid (I := I) (M := M) α) = 0 := by
    rw [MeasureTheory.Measure.restrict_apply hN_meas] at hN_null_restricted
    exact hN_null_restricted
  have hpre_null := riemannianVolumeMeasure_pullback_null
    (I := I) (M := M) g α hN_meas hN_null
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ hpre_null
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  by_cases hx_src : x ∈ (chartAt H α).source
  · refine ⟨hx_src, ?_⟩
    simp only [Set.mem_setOf_eq]
    by_contra h_not_in_N
    have h_y_in_target :
        (toEuclidean (E := E)) ((extChartAt I α) x) ∈
          chartTargetEuclid (I := I) (M := M) α := by
      refine ⟨(extChartAt I α) x, ?_, rfl⟩
      have h_src_ext : x ∈ (extChartAt I α).source := by
        rwa [extChartAt_source_eq_chartAt_source]
      exact (extChartAt I α).map_source h_src_ext
    have h_y_not_bad :
        (toEuclidean (E := E)) ((extChartAt I α) x) ∉ badSet := fun hyb =>
      h_not_in_N (h_bad_sub_N hyb)
    have h_chart_agree :
        hessPairingChartLocal (I := I) (M := M) g α φ
            (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
            ((toEuclidean (E := E)) ((extChartAt I α) x)) =
          smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) ((extChartAt I α) x)) := by
      by_contra hne
      exact h_y_not_bad hne
    apply hx
    rw [hessPairingMChartContribution_eq_on_source (I := I) (M := M) g φ α
      (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) hx_src]
    rw [h_chart_agree]
  · exfalso
    apply hx
    rw [hessPairingMChartContribution_zero_off_source (I := I) (M := M) g φ α
      (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) hx_src]
    have h_pou_subord :
        tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
          (chartAt H α).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
    have hx_notsupp : x ∉ tsupport
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := fun h => hx_src (h_pou_subord h)
    have hρ_zero : (chartAtlasPOU I M α : M → ℝ) x = 0 :=
      image_eq_zero_of_notMem_tsupport hx_notsupp
    rw [hρ_zero]
    ring

def perChartAeTransferableSmoothCase
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    Prop :=
  ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    hessPairingMChartContribution (I := I) (M := M) g φ α
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
      =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => (chartAtlasPOU I M α : M → ℝ) x *
        smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
          ((toEuclidean (E := E)) (extChartAt I α x)))

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma perChartAeTransferableSmoothCase_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    perChartAeTransferableSmoothCase (I := I) (M := M) g φ v ↔
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        hessPairingMChartContribution (I := I) (M := M) g φ α
            (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
          =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
          (fun x : M => (chartAtlasPOU I M α : M → ℝ) x *
            smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
              ((toEuclidean (E := E)) (extChartAt I α x))) := Iff.rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem perChartAeTransferableSmoothCase_holds
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    perChartAeTransferableSmoothCase (I := I) (M := M) g φ v := by
  intro α _hα
  exact perChartAeTransferable_smoothCase (I := I) (M := M) g φ v α

omit [NeZero (Module.finrank ℝ E)] in
theorem hessPairingMOnLapDom_aeEq_pou_weighted_euclid_pairing_smoothCase_of_transferable
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v) :
    hessPairingMOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
      =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x))) := by
  classical
  have h_union_null :
      (riemannianVolumeMeasure (I := I) (M := M) g)
        (⋃ α ∈ chartAtlasPOU_finset (I := I) (M := M),
          {x : M |
            hessPairingMChartContribution (I := I) (M := M) g φ α
                (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x ≠
              (chartAtlasPOU I M α : M → ℝ) x *
                smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
                  ((toEuclidean (E := E)) (extChartAt I α x))}) = 0 := by
    have h_count : (chartAtlasPOU_finset (I := I) (M := M) : Set M).Countable :=
      (chartAtlasPOU_finset (I := I) (M := M)).countable_toSet
    refine (MeasureTheory.measure_biUnion_null_iff h_count).mpr ?_
    intro α hα
    have h_ae := h_transfer α hα
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff] at h_ae
    exact h_ae
  have h_all_ae : ∀ᵐ x ∂(riemannianVolumeMeasure (I := I) (M := M) g),
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        hessPairingMChartContribution (I := I) (M := M) g φ α
            (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x =
          (chartAtlasPOU I M α : M → ℝ) x *
            smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
              ((toEuclidean (E := E)) (extChartAt I α x)) := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ h_union_null
    intro x hx
    simp only [Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨α, hα_in_finset, hα_ne⟩ := hx
    simp only [Set.mem_iUnion]
    exact ⟨α, hα_in_finset, hα_ne⟩
  filter_upwards [h_all_ae] with x h_x_per_chart
  rw [hessPairingMOnLapDom_def
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) x]
  apply Finset.sum_congr rfl
  intro α hα
  exact h_x_per_chart α hα

theorem hessPairingMOnLapDom_aeEq_hessPairingChart_smoothCase_of_both
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    hessPairingMOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
      =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) := by
  classical
  have h_step1 := hessPairingMOnLapDom_aeEq_pou_weighted_euclid_pairing_smoothCase_of_transferable
    (I := I) (M := M) g φ v h_transfer
  have h_pointwise : ∀ x : M,
      (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x))) =
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) x :=
    pou_weighted_euclid_pairing_eq_hessPairingChart_pointwise_of_discharge
      (I := I) (M := M) g φ v h_discharge
  filter_upwards [h_step1] with x hx_eq1
  rw [hx_eq1]
  exact h_pointwise x

theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_of_both
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      hessPairingSmoothLp (I := I) (M := M) g φ v :=
  hessPairingLpOnLapDom_eq_hessPairingSmoothLp_of_globalHypothesis
    (I := I) (M := M) g φ v
    (hessPairingMOnLapDom_aeEq_hessPairingChart_smoothCase_of_both
      (I := I) (M := M) g φ v h_transfer h_discharge)

theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_connector
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1
          (DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity.smoothToH1Compl_mem_laplacianDomainPow_two
            (I := I) (M := M) g v)) =
      hessPairingSmoothLp (I := I) (M := M) g φ v :=
  hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_of_both
    (I := I) (M := M) g φ v h_transfer h_discharge

omit [NeZero (Module.finrank ℝ E)] in
theorem hessPairingMOnLapDom_aeEq_pou_weighted_euclid_pairing_smoothCase
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    hessPairingMOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
      =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (chartAtlasPOU I M α : M → ℝ) x *
          smoothEuclidHessianPairingChart (I := I) (M := M) g α φ v
            ((toEuclidean (E := E)) (extChartAt I α x))) :=
  hessPairingMOnLapDom_aeEq_pou_weighted_euclid_pairing_smoothCase_of_transferable
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v)

theorem hessPairingMOnLapDom_aeEq_hessPairingChart_smoothCase_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    hessPairingMOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v)
      =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v) :=
  hessPairingMOnLapDom_aeEq_hessPairingChart_smoothCase_of_both
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v) h_discharge

theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      hessPairingSmoothLp (I := I) (M := M) g φ v :=
  hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_of_both
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v) h_discharge

theorem hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_connector_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    hessPairingLpOnLapDom (I := I) (M := M) g φ
        (DifferentialGeometry.Analysis.Laplacian.laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1
          (DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity.smoothToH1Compl_mem_laplacianDomainPow_two
            (I := I) (M := M) g v)) =
      hessPairingSmoothLp (I := I) (M := M) g φ v :=
  hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_connector
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v) h_discharge

end HessianBridgeSmoothLp
end Laplacian
end Analysis
end DifferentialGeometry

end
