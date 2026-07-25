import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.WeakSolution.WeakSolutionHeadline

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv
open DifferentialGeometry.Analysis.Laplacian.ChartLocalLaplacian
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

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
local notation "chartHaar" =>
  MeasureTheory.Measure.map (toEuclidean : E → EuclN) (modelHaar (E := E))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
private lemma euclidPartial_eq_zero_of_notMem_tsupport
    {u : EuclN → ℝ} (l : Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∉ tsupport u) :
    euclidPartial (E := E) l u y = 0 := by
  classical
  have hopen_c : IsOpen (tsupport u)ᶜ := (isClosed_tsupport u).isOpen_compl
  have hu_evt : u =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) :=
    Filter.eventually_of_mem (hopen_c.mem_nhds hy)
      (fun z hz => image_eq_zero_of_notMem_tsupport hz)
  rw [euclidPartial_def, Filter.EventuallyEq.fderiv_eq hu_evt,
    fderiv_const_apply, ContinuousLinearMap.zero_apply]

omit [CompleteSpace E] in
theorem tensorComponent_chartBilinIdentity_of_dirichlet
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    {K : Set EuclN} (hK : IsCompact K)
    (hK_target : K ⊆ chartTargetEuclid (I := I) (M := M) α)
    (P₀ : CompIdx E r s)
    (hT_supp : tsupport T.toFun ⊆ (chartAt H α).source)
    (hT_K : tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) ⊆ K)
    {φ : EuclN → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_cs : HasCompactSupport φ)
    (hφ_supp : tsupport φ ⊆ chartTargetEuclid (I := I) (M := M) α) :
    (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).bilin
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ =
      (∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T
          (rotatedTestSection (I := I) (M := M) g r s α P₀
            (chartTestPullback (I := I) (M := M) α φ)
            (chartTestPullback_contMDiffOn (I := I) (M := M) α hφ)
            (chartTestPullback_tsupport_subset_source (I := I) (M := M) α hφ_cs
              hφ_supp)) x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
      (∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y
        ∂(volume : Measure EuclN)) -
      (∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y * φ y
        ∂(volume : Measure EuclN)) +
      ∫ y, (∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y) * φ y
        ∂(volume : Measure EuclN) := by
  classical
  have hcTE_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hcTE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    hcTE_open.measurableSet
  have hφ' : ContDiff ℝ ∞ φ := hφ
  have hχs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (chartTestPullback (I := I) (M := M) α φ)
      (chartAt H α).source :=
    chartTestPullback_contMDiffOn (I := I) (M := M) α hφ
  have hχt : tsupport (chartTestPullback (I := I) (M := M) α φ) ⊆
      (chartAt H α).source :=
    chartTestPullback_tsupport_subset_source (I := I) (M := M) α hφ_cs hφ_supp
  have hdensity : ContDiffOn ℝ ∞ (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    densityOnEuclid_contDiffOn (I := I) g α
  have hbump_eqOn : Set.EqOn
      (chartPushedRaw I α (chartTestPullback (I := I) (M := M) α φ)) φ
      (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushedRaw_chartTestPullback_eqOn (I := I) (M := M) α φ
  have hbump_partial_eqOn : ∀ l : Fin (Module.finrank ℝ E),
      Set.EqOn (euclidPartial (E := E) l
          (chartPushedRaw I α (chartTestPullback (I := I) (M := M) α φ)))
        (euclidPartial (E := E) l φ)
        (chartTargetEuclid (I := I) (M := M) α) := fun l =>
    euclidPartial_chartPushedRaw_chartTestPullback_eqOn (I := I) (M := M) α φ l
  have hdφ : ∀ l : Fin (Module.finrank ℝ E),
      ContDiff ℝ ∞ (euclidPartial (E := E) l φ) := by
    intro l
    rw [show euclidPartial (E := E) l φ =
        (fun L : EuclN →L[ℝ] ℝ => L (EuclideanSpace.single l 1)) ∘
          (fun z => fderiv ℝ φ z) from by funext z; rfl]
    exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l 1)).contDiff.comp
      (hφ'.fderiv_right (m := ∞) (by rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]))
  have hcs_dφ : ∀ l : Fin (Module.finrank ℝ E),
      HasCompactSupport (euclidPartial (E := E) l φ) := by
    intro l
    refine HasCompactSupport.of_support_subset_isCompact (K := tsupport φ)
      hφ_cs ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyφ
    exact hy (euclidPartial_eq_zero_of_notMem_tsupport (E := E) l hyφ)
  have hdφ_supp : ∀ l : Fin (Module.finrank ℝ E),
      tsupport (euclidPartial (E := E) l φ) ⊆
        chartTargetEuclid (I := I) (M := M) α := by
    intro l
    refine (closure_minimal ?_ (isClosed_tsupport φ)).trans hφ_supp
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hz'
    exact hz (euclidPartial_eq_zero_of_notMem_tsupport (E := E) l hz')
  have hφ_partial_zero : ∀ l : Fin (Module.finrank ℝ E), ∀ y, y ∉ tsupport φ →
      euclidPartial (E := E) l φ y = 0 := fun l y hy =>
    euclidPartial_eq_zero_of_notMem_tsupport (E := E) l hy
  have hu_partial_zero : ∀ k : Fin (Module.finrank ℝ E), ∀ y,
      y ∉ tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) →
      euclidPartial (E := E) k
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) y = 0 :=
    fun k y hy => euclidPartial_eq_zero_of_notMem_tsupport (E := E) k hy
  have hP_prc : ContDiff ℝ ∞
      (fun y => densityOnEuclid (I := I) g α y *
        covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y) :=
    contDiff_mul_chartTest (I := I) (M := M) α
      (hdensity.mul (covPrincipalRotationCoeff_contDiffOn (I := I) (M := M)
        g r s T α P₀)) hφ' hφ_supp
  have hP_lov : ContDiff ℝ ∞
      (fun y => densityOnEuclid (I := I) g α y *
        covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
          φ y) :=
    contDiff_mul_chartTest (I := I) (M := M) α
      (hdensity.mul (covLowerOrderRotationValueCoeff_contDiffOn (I := I) (M := M)
        g r s T α P₀)) hφ' hφ_supp
  have hP_grad : ∀ l : Fin (Module.finrank ℝ E), ContDiff ℝ ∞
      (fun y => weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
        euclidPartial (E := E) l φ y) := fun l =>
    contDiff_mul_chartTest (I := I) (M := M) α
      (weightedGradCoeff_contDiffOn (I := I) (M := M) g r s T α P₀ l) (hdφ l)
      (hdφ_supp l)
  have hP_ibp : ∀ l : Fin (Module.finrank ℝ E), ContDiff ℝ ∞
      (fun y => euclidPartial (E := E) l
          (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y) :=
    fun l => contDiff_mul_chartTest (I := I) (M := M) α
      (euclidPartial_contDiffOn_chartTarget (I := I) (M := M) α l
        (weightedGradCoeff_contDiffOn (I := I) (M := M) g r s T α P₀ l)) hφ'
      hφ_supp
  have hP_principal : ContDiff ℝ ∞
      ((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ) := by
    have hu_cd : ContDiff ℝ ∞
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) :=
      tensorComponentEuclid_contDiff (I := I) (M := M) g r s T α P₀ hT_supp
    have hbody : ContDiff ℝ ∞
        (fun x => ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).a x i j *
              ((fderiv ℝ (tensorComponentEuclid (I := I) (M := M)
                g r s T α P₀) x) (EuclideanSpace.single i 1)) *
              ((fderiv ℝ φ x) (EuclideanSpace.single j 1))) :=
      ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
        (((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).contDiff_a
          i j).mul ((hu_cd.fderiv_right (m := ∞)
          (by rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl])).clm_apply
          contDiff_const)).mul ((hφ'.fderiv_right (m := ∞)
          (by rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl])).clm_apply
          contDiff_const)))
    exact hbody
  have hcs_mul : ∀ h : EuclN → ℝ,
      HasCompactSupport (fun y => h y * φ y) := fun h =>
    hasCompactSupport_mul_chartTest (E := E) hφ_cs
  have hcs_principal : HasCompactSupport
      ((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀))
      (IsCompact.of_isClosed_subset hK (isClosed_tsupport _) hT_K) ?_
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hyu
    apply hy
    rw [SmoothEllipticBilinearForm.principalIntegrand]
    refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
    have := hu_partial_zero i y hyu
    rw [euclidPartial_def] at this
    rw [this]; ring
  have hint_principal : Integrable
      ((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ)
      (volume : Measure EuclN) :=
    integrable_of_contDiff_hasCompactSupport (E := E) hP_principal hcs_principal
  have hint_prc : Integrable
      (fun y => densityOnEuclid (I := I) g α y *
        covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y)
      (volume : Measure EuclN) := by
    have heq : (fun y => densityOnEuclid (I := I) g α y *
        covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y) =
      (fun y => (densityOnEuclid (I := I) g α y *
        covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y) * φ y) := by
      funext y; ring
    exact integrable_of_contDiff_hasCompactSupport (E := E) hP_prc
      (heq ▸ hcs_mul _)
  have hint_lov : Integrable
      (fun y => densityOnEuclid (I := I) g α y *
        covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y * φ y)
      (volume : Measure EuclN) := by
    have heq : (fun y => densityOnEuclid (I := I) g α y *
        covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y * φ y) =
      (fun y => (densityOnEuclid (I := I) g α y *
        covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y) *
          φ y) := by
      funext y; ring
    exact integrable_of_contDiff_hasCompactSupport (E := E) hP_lov
      (heq ▸ hcs_mul _)
  have hint_grad : ∀ l : Fin (Module.finrank ℝ E), Integrable
      (fun y => weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
        euclidPartial (E := E) l φ y) (volume : Measure EuclN) := fun l =>
    integrable_of_contDiff_hasCompactSupport (E := E) (hP_grad l)
      (hasCompactSupport_mul_chartTest (E := E) (hcs_dφ l))
  have hint_ibp : ∀ l : Fin (Module.finrank ℝ E), Integrable
      (fun y => euclidPartial (E := E) l
          (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y)
      (volume : Measure EuclN) := fun l =>
    integrable_of_contDiff_hasCompactSupport (E := E) (hP_ibp l) (hcs_mul _)
  have hsetInt_to_int : ∀ X : EuclN → ℝ,
      (∀ y, y ∉ chartTargetEuclid (I := I) (M := M) α → X y = 0) →
      ∫ y in chartTargetEuclid (I := I) (M := M) α, X y ∂chartHaar =
        ∫ y, X y ∂(volume : Measure EuclN) := by
    intro X hX_zero
    rw [DifferentialGeometry.Integral.Measure.map_toEuclidean_modelHaar_eq_volume
      (E := E)]
    exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hX_zero
  set vRot : SmoothCcTensor g r s :=
    rotatedTestSection (I := I) (M := M) g r s α P₀
      (chartTestPullback (I := I) (M := M) α φ) hχs hχt with hvRot_def
  have hsource : ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T
        vRot x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (covPrincipalIntegrand (I := I) (M := M) g r s T vRot α y +
            covLowerOrderIntegrand (I := I) (M := M) g r s T vRot α y)
        ∂chartHaar :=
    tensorCovDerivPointwiseInner_integral_chart_pull (I := I) (M := M)
      g r s T vRot α hT_supp
  have hLHS_integrand : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      densityOnEuclid (I := I) g α y *
          (covPrincipalIntegrand (I := I) (M := M) g r s T vRot α y +
            covLowerOrderIntegrand (I := I) (M := M) g r s T vRot α y) =
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
            (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y +
          (densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y +
          (densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
              φ y +
          ∑ l : Fin (Module.finrank ℝ E),
            densityOnEuclid (I := I) g α y *
              covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
                euclidPartial (E := E) l φ y)) := by
    intro y hy
    have hPI : (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y =
        densityOnEuclid (I := I) g α y *
          (∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                  euclidPartial (E := E) k
                    (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) y *
                euclidPartial (E := E) l φ y) :=
      (density_scalarPrincipal_eq_principalIntegrand (I := I) (M := M) g α hK
        hK_target hT_K φ hy).symm
    have hscalar : ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
                euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M)
                      g r s T α P₀.1 P₀.2)) y *
              euclidPartial (E := E) l
                (chartPushedRaw I α (chartTestPullback (I := I) (M := M) α φ))
                y =
        ∑ k : Fin (Module.finrank ℝ E),
          ∑ l : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α k l y *
                euclidPartial (E := E) k
                  (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) y *
              euclidPartial (E := E) l φ y := by
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
      rw [show chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α P₀.1 P₀.2) =
          tensorComponentEuclid (I := I) (M := M) g r s T α P₀ from
        (tensorComponentEuclid_def (I := I) (M := M) g r s T α P₀).symm,
        hbump_partial_eqOn l hy]
    have hgrad : ∑ l : Fin (Module.finrank ℝ E),
          covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
            euclidPartial (E := E) l
              (chartPushedRaw I α (chartTestPullback (I := I) (M := M) α φ)) y =
        ∑ l : Fin (Module.finrank ℝ E),
          covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
            euclidPartial (E := E) l φ y := by
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [hbump_partial_eqOn l hy]
    rw [hvRot_def,
      covPrincipalIntegrand_rotated_collapse (I := I) (M := M) g r s T α P₀
        hχs hχt hy,
      covPrincipalRotationRemainder_eq_coeff_mul (I := I) (M := M) g r s T α P₀
        hχs hχt y,
      covLowerOrderIntegrand_rotated_collapse (I := I) (M := M) g r s T α P₀
        hχs hχt hy,
      hscalar, hgrad, hbump_eqOn hy, hPI]
    simp only [mul_add, Finset.mul_sum]
    ring
  have hLHS_setInt :
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (covPrincipalIntegrand (I := I) (M := M) g r s T vRot α y +
            covLowerOrderIntegrand (I := I) (M := M) g r s T vRot α y)
        ∂chartHaar =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        ((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
            (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y +
          (densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y +
          (densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
              φ y +
          ∑ l : Fin (Module.finrank ℝ E),
            densityOnEuclid (I := I) g α y *
              covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
                euclidPartial (E := E) l φ y))) ∂chartHaar :=
    MeasureTheory.setIntegral_congr_fun hcTE_meas hLHS_integrand
  have hsum_zero : ∀ y, y ∉ chartTargetEuclid (I := I) (M := M) α →
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y +
        (densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y +
        (densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
            φ y +
        ∑ l : Fin (Module.finrank ℝ E),
          densityOnEuclid (I := I) g α y *
            covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
              euclidPartial (E := E) l φ y)) = 0 := by
    intro y hy
    have hyφ : y ∉ tsupport φ := fun h => hy (hφ_supp h)
    have hyu : y ∉ tsupport (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) :=
      fun h => hy ((hT_K.trans hK_target) h)
    have hφ0 : φ y = 0 := image_eq_zero_of_notMem_tsupport hyφ
    have hprinc0 :
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y = 0 := by
      rw [SmoothEllipticBilinearForm.principalIntegrand]
      refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
      have := hu_partial_zero i y hyu
      rw [euclidPartial_def] at this
      rw [this]; ring
    rw [hprinc0, hφ0]
    simp only [mul_zero, zero_add]
    exact Finset.sum_eq_zero (fun l _ => by
      rw [hφ_partial_zero l y hyφ]; ring)
  have hLHS_volume :
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T vRot x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y, ((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y +
        (densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y +
        (densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
            φ y +
        ∑ l : Fin (Module.finrank ℝ E),
          densityOnEuclid (I := I) g α y *
            covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
              euclidPartial (E := E) l φ y))) ∂(volume : Measure EuclN) := by
    rw [hsource, hLHS_setInt]
    exact hsetInt_to_int _ hsum_zero
  have hint_gradsum : Integrable
      (fun y => ∑ l : Fin (Module.finrank ℝ E),
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
            euclidPartial (E := E) l φ y) (volume : Measure EuclN) := by
    refine MeasureTheory.integrable_finset_sum _ (fun l _ => ?_)
    have heq : (fun y => densityOnEuclid (I := I) g α y *
        covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
          euclidPartial (E := E) l φ y) =
      (fun y => weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
        euclidPartial (E := E) l φ y) := by
      funext y; rw [weightedGradCoeff_eq]
    rw [heq]; exact hint_grad l
  have hLHS_split :
      ∫ y, ((tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y +
        (densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y +
        (densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
            φ y +
        ∑ l : Fin (Module.finrank ℝ E),
          densityOnEuclid (I := I) g α y *
            covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
              euclidPartial (E := E) l φ y))) ∂(volume : Measure EuclN) =
      (∫ y, (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y
          ∂(volume : Measure EuclN)) +
      ((∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y
          ∂(volume : Measure EuclN)) +
      ((∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y * φ y
          ∂(volume : Measure EuclN)) +
      ∫ y, (∑ l : Fin (Module.finrank ℝ E),
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
            euclidPartial (E := E) l φ y) ∂(volume : Measure EuclN))) := by
    rw [MeasureTheory.integral_add
        (f := (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ)
        (g := fun y => densityOnEuclid (I := I) g α y *
            covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y +
          (densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
              φ y +
          ∑ l : Fin (Module.finrank ℝ E),
            densityOnEuclid (I := I) g α y *
              covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
                euclidPartial (E := E) l φ y))
        hint_principal (hint_prc.add (hint_lov.add hint_gradsum)),
      MeasureTheory.integral_add
        (f := fun y => densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y)
        (g := fun y => densityOnEuclid (I := I) g α y *
            covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y *
              φ y +
          ∑ l : Fin (Module.finrank ℝ E),
            densityOnEuclid (I := I) g α y *
              covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
                euclidPartial (E := E) l φ y)
        hint_prc (hint_lov.add hint_gradsum),
      MeasureTheory.integral_add
        (f := fun y => densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y * φ y)
        (g := fun y => ∑ l : Fin (Module.finrank ℝ E),
          densityOnEuclid (I := I) g α y *
            covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
              euclidPartial (E := E) l φ y)
        hint_lov hint_gradsum]
  have hgradsum_eq :
      ∫ y, (∑ l : Fin (Module.finrank ℝ E),
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
            euclidPartial (E := E) l φ y) ∂(volume : Measure EuclN) =
      ∑ l : Fin (Module.finrank ℝ E),
        ∫ y, weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
          euclidPartial (E := E) l φ y ∂(volume : Measure EuclN) := by
    rw [MeasureTheory.integral_finset_sum _ (fun l _ => by
      have heq : (fun y => densityOnEuclid (I := I) g α y *
          covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
            euclidPartial (E := E) l φ y) =
        (fun y => weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
          euclidPartial (E := E) l φ y) := by funext y; rw [weightedGradCoeff_eq]
      rw [heq]; exact hint_grad l)]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y; rw [weightedGradCoeff_eq]
  have hIBP : ∀ l : Fin (Module.finrank ℝ E),
      ∫ y, weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
        euclidPartial (E := E) l φ y ∂(volume : Measure EuclN) =
      -∫ y, euclidPartial (E := E) l
          (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y
        ∂(volume : Measure EuclN) := by
    intro l
    have hL : ∫ y, weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
        euclidPartial (E := E) l φ y ∂(volume : Measure EuclN) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        weightedGradCoeff (I := I) (M := M) g r s T α P₀ l y *
          euclidPartial (E := E) l φ y ∂chartHaar :=
      (hsetInt_to_int _ (fun y hy => by
        rw [hφ_partial_zero l y (fun h => hy (hφ_supp h)), mul_zero])).symm
    have hR : ∫ y, euclidPartial (E := E) l
        (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y
        ∂(volume : Measure EuclN) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        euclidPartial (E := E) l
          (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y
        ∂chartHaar :=
      (hsetInt_to_int _ (fun y hy => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hφ_supp h)),
          mul_zero])).symm
    rw [hL, hR]
    exact chartTarget_integral_byParts (I := I) (M := M) α l
      (weightedGradCoeff_contDiffOn (I := I) (M := M) g r s T α P₀ l)
      hφ'.contDiffOn hφ_cs hφ_supp
  have hbilin_eq :
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).bilin
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ =
        ∫ y, (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y
          ∂(volume : Measure EuclN) := by
    rw [SmoothEllipticBilinearForm.bilin, MeasureTheory.setIntegral_univ]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y
    change (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y +
        (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).c y *
          tensorComponentEuclid (I := I) (M := M) g r s T α P₀ y * φ y =
      (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
        (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y
    rw [tensorPrincipalForm_c_apply (I := I) (M := M) g α hK hK_target y]
    ring
  have hgrad_int : ∑ l : Fin (Module.finrank ℝ E),
        ∫ y, euclidPartial (E := E) l
          (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y
          ∂(volume : Measure EuclN) =
      ∫ y, (∑ l : Fin (Module.finrank ℝ E),
        euclidPartial (E := E) l
          (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y) * φ y
        ∂(volume : Measure EuclN) := by
    have hdist : (fun y => (∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y) * φ y) =
        (fun y => ∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y * φ y) := by
      funext y
      rw [Finset.sum_mul]
    rw [hdist, MeasureTheory.integral_finset_sum _ (fun l _ => hint_ibp l)]
  have hgradsum_ibp :
      ∫ y, (∑ l : Fin (Module.finrank ℝ E),
        densityOnEuclid (I := I) g α y *
          covLowerOrderRotationGradCoeff (I := I) (M := M) g r s T α P₀ l y *
            euclidPartial (E := E) l φ y) ∂(volume : Measure EuclN) =
      -∫ y, (∑ l : Fin (Module.finrank ℝ E),
        euclidPartial (E := E) l
          (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y) * φ y
        ∂(volume : Measure EuclN) := by
    rw [hgradsum_eq,
      Finset.sum_congr rfl (fun l (_ : l ∈ Finset.univ) => hIBP l),
      Finset.sum_neg_distrib, hgrad_int]
  have hsource_eq :
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g r s T vRot x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      (∫ y, (tensorPrincipalForm (I := I) (M := M) g α hK hK_target).principalIntegrand
          (tensorComponentEuclid (I := I) (M := M) g r s T α P₀) φ y
          ∂(volume : Measure EuclN)) +
      ((∫ y, densityOnEuclid (I := I) g α y *
          covPrincipalRotationCoeff (I := I) (M := M) g r s T α P₀ y * φ y
          ∂(volume : Measure EuclN)) +
      ((∫ y, densityOnEuclid (I := I) g α y *
          covLowerOrderRotationValueCoeff (I := I) (M := M) g r s T α P₀ y * φ y
          ∂(volume : Measure EuclN)) +
      -∫ y, (∑ l : Fin (Module.finrank ℝ E),
          euclidPartial (E := E) l
            (weightedGradCoeff (I := I) (M := M) g r s T α P₀ l) y) * φ y
        ∂(volume : Measure EuclN))) := by
    rw [hLHS_volume, hLHS_split, hgradsum_ibp]
  rw [hbilin_eq]
  linarith [hsource_eq]

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
