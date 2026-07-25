import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ChartForm


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def covLowerOrderIntegrand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
      ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                (euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s S α P.1 P.2)) y *
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α l Q.1 Q.2 y
                  + covDerivLowerOrderTerm (I := I) (M := M)
                        g r s S α k P.1 P.2 y *
                      euclidPartial (E := E) l
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s T α Q.1 Q.2)) y
                  + covDerivLowerOrderTerm (I := I) (M := M)
                        g r s S α k P.1 P.2 y *
                      covDerivLowerOrderTerm (I := I) (M := M)
                        g r s T α l Q.1 Q.2 y)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma covLowerOrderIntegrand_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covLowerOrderIntegrand (I := I) (M := M) g r s S T α y =
      ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                  (euclidPartial (E := E) k
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s S α P.1 P.2)) y *
                      covDerivLowerOrderTerm (I := I) (M := M)
                        g r s T α l Q.1 Q.2 y
                    + covDerivLowerOrderTerm (I := I) (M := M)
                          g r s S α k P.1 P.2 y *
                        euclidPartial (E := E) l
                          (chartPushedRaw I α
                            (tensorChartComponentRaw (I := I) (M := M)
                              g r s T α Q.1 Q.2)) y
                    + covDerivLowerOrderTerm (I := I) (M := M)
                          g r s S α k P.1 P.2 y *
                        covDerivLowerOrderTerm (I := I) (M := M)
                          g r s T α l Q.1 Q.2 y) := rfl

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivPointwiseInner_chart_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      covPrincipalIntegrand (I := I) (M := M) g r s S T α y +
        covLowerOrderIntegrand (I := I) (M := M) g r s S T α y := by
  classical
  rw [tensorCovDerivPointwiseInner_chart_eq_component_sum (I := I) (M := M)
    g r s S T α hy]
  rw [covPrincipalIntegrand_def, covLowerOrderIntegrand_def]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem chartPushedRaw_tensorChartComponentRaw_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (chartPushedRaw I α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hraw_src : ContMDiffOn I 𝓘(ℝ) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      ((chartAt H α).source) :=
    tensorChartComponentRaw_contMDiffOn_chart_source (I := I) (M := M)
      g r s S α Idx Jdx
  have hraw_extsrc : ContMDiffOn I 𝓘(ℝ) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      ((extChartAt I α).source) := by
    rw [extChartAt_source]; exact hraw_src
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (extChartAt I α).source := fun y hy => (extChartAt I α).map_target hy
  have hcomp_E : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target :=
    hraw_extsrc.comp hsymm hmaps
  have hcontDiff_E : ContDiffOn ℝ ∞
      ((tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target :=
    hcomp_E.contDiffOn
  have hcomp_eucl : ContDiffOn ℝ ∞
      (((tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) ∘
          (extChartAt I α).symm) ∘
        (toEuclidean.symm :
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine hcontDiff_E.comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
  refine hcomp_eucl.congr (fun z hz => ?_)
  exact chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hz

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem euclidPartial_chartPushedRaw_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (k : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (euclidPartial (E := E) k
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)))
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartPushedRaw I α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) with hu_def
  have hu : ContDiffOn ℝ ∞ u (chartTargetEuclid (I := I) (M := M) α) :=
    chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
      g r s S α Idx Jdx
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hfderiv : ContDiffOn ℝ ∞ (fun z => fderiv ℝ u z)
      (chartTargetEuclid (I := I) (M := M) α) := by
    have hsucc : ContDiffOn ℝ ((∞ : WithTop ℕ∞) + 1) u
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]; exact hu
    have hfw : ContDiffOn ℝ ∞ (fderivWithin ℝ u
        (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_succ_iff_fderivWithin hopen.uniqueDiffOn).mp hsucc).2.2
    refine hfw.congr (fun z hz => ?_)
    exact (fderivWithin_of_isOpen (f := u) (𝕜 := ℝ) hopen hz).symm
  have hcomp : ContDiffOn ℝ ∞
      ((fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
          L (EuclideanSpace.single k 1)) ∘ (fun z => fderiv ℝ u z))
      (chartTargetEuclid (I := I) (M := M) α) :=
    (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single k 1)).contDiff.comp_contDiffOn hfderiv
  refine hcomp.congr (fun z _ => ?_)
  rw [hu_def]
  rfl

omit [CompleteSpace E] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covLowerOrderIntegrand_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M) :
    ContDiffOn ℝ ∞
      (covLowerOrderIntegrand (I := I) (M := M) g r s S T α)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hrawS : ∀ (Idx' : Fin r → Fin (Module.finrank ℝ E))
      (Jdx' : Fin s → Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx'))
        (chartTargetEuclid (I := I) (M := M) α) := fun Idx' Jdx' =>
    chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
      g r s S α Idx' Jdx'
  have hrawT : ∀ (Idx' : Fin r → Fin (Module.finrank ℝ E))
      (Jdx' : Fin s → Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞
        (chartPushedRaw I α
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx' Jdx'))
        (chartTargetEuclid (I := I) (M := M) α) := fun Idx' Jdx' =>
    chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M)
      g r s T α Idx' Jdx'
  have hsummand : ∀ P Q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                  (euclidPartial (E := E) k
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s S α P.1 P.2)) y *
                      covDerivLowerOrderTerm (I := I) (M := M)
                        g r s T α l Q.1 Q.2 y
                    + covDerivLowerOrderTerm (I := I) (M := M)
                          g r s S α k P.1 P.2 y *
                        euclidPartial (E := E) l
                          (chartPushedRaw I α
                            (tensorChartComponentRaw (I := I) (M := M)
                              g r s T α Q.1 Q.2)) y
                    + covDerivLowerOrderTerm (I := I) (M := M)
                          g r s S α k P.1 P.2 y *
                        covDerivLowerOrderTerm (I := I) (M := M)
                          g r s T α l Q.1 Q.2 y))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro P Q
    have hgram : ContDiffOn ℝ ∞
        (covChartMetricGram (I := I) (M := M) g r s α P Q)
        (chartTargetEuclid (I := I) (M := M) α) :=
      covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q
    have hinner : ∀ k l : Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            chartInvGramEuclid (I := I) g α k l y *
              (euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s S α P.1 P.2)) y *
                  covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α l Q.1 Q.2 y
                + covDerivLowerOrderTerm (I := I) (M := M)
                      g r s S α k P.1 P.2 y *
                    euclidPartial (E := E) l
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s T α Q.1 Q.2)) y
                + covDerivLowerOrderTerm (I := I) (M := M)
                      g r s S α k P.1 P.2 y *
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α l Q.1 Q.2 y))
          (chartTargetEuclid (I := I) (M := M) α) := by
      intro k l
      have hGinv : ContDiffOn ℝ ∞ (chartInvGramEuclid (I := I) g α k l)
          (chartTargetEuclid (I := I) (M := M) α) :=
        chartInvGramEuclid_contDiffOn (I := I) (M := M) g α k l
      have hSpartial : ContDiffOn ℝ ∞
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S α P.1 P.2)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M)
          g r s S α k P.1 P.2
      have hTpartial : ContDiffOn ℝ ∞
          (euclidPartial (E := E) l
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s T α Q.1 Q.2)))
          (chartTargetEuclid (I := I) (M := M) α) :=
        euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M)
          g r s T α l Q.1 Q.2
      have hSlo : ContDiffOn ℝ ∞
          (covDerivLowerOrderTerm (I := I) (M := M) g r s S α k P.1 P.2)
          (chartTargetEuclid (I := I) (M := M) α) :=
        covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M)
          g r s S α k P.1 P.2 hrawS
      have hTlo : ContDiffOn ℝ ∞
          (covDerivLowerOrderTerm (I := I) (M := M) g r s T α l Q.1 Q.2)
          (chartTargetEuclid (I := I) (M := M) α) :=
        covDerivComponent_lowerOrder_contDiffOn (I := I) (M := M)
          g r s T α l Q.1 Q.2 hrawT
      exact hGinv.mul (((hSpartial.mul hTlo).add (hSlo.mul hTpartial)).add
        (hSlo.mul hTlo))
    have hklsum : ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                (euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s S α P.1 P.2)) y *
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α l Q.1 Q.2 y
                  + covDerivLowerOrderTerm (I := I) (M := M)
                        g r s S α k P.1 P.2 y *
                      euclidPartial (E := E) l
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s T α Q.1 Q.2)) y
                  + covDerivLowerOrderTerm (I := I) (M := M)
                        g r s S α k P.1 P.2 y *
                      covDerivLowerOrderTerm (I := I) (M := M)
                        g r s T α l Q.1 Q.2 y))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ContDiffOn.sum (fun k _ => ContDiffOn.sum (fun l _ => hinner k l))
    exact hgram.mul hklsum
  have hsum : ContDiffOn ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              ∑ k : Fin (Module.finrank ℝ E),
                ∑ l : Fin (Module.finrank ℝ E),
                  chartInvGramEuclid (I := I) g α k l y *
                    (euclidPartial (E := E) k
                          (chartPushedRaw I α
                            (tensorChartComponentRaw (I := I) (M := M)
                              g r s S α P.1 P.2)) y *
                        covDerivLowerOrderTerm (I := I) (M := M)
                          g r s T α l Q.1 Q.2 y
                      + covDerivLowerOrderTerm (I := I) (M := M)
                            g r s S α k P.1 P.2 y *
                          euclidPartial (E := E) l
                            (chartPushedRaw I α
                              (tensorChartComponentRaw (I := I) (M := M)
                                g r s T α Q.1 Q.2)) y
                      + covDerivLowerOrderTerm (I := I) (M := M)
                            g r s S α k P.1 P.2 y *
                          covDerivLowerOrderTerm (I := I) (M := M)
                            g r s T α l Q.1 Q.2 y))
      (chartTargetEuclid (I := I) (M := M) α) :=
    ContDiffOn.sum (fun P _ => ContDiffOn.sum (fun Q _ => hsummand P Q))
  exact hsum

omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covLowerOrderIntegrand_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M) :
    Set.EqOn (covLowerOrderIntegrand (I := I) (M := M) g r s S T α)
      (fun y => tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) -
          covPrincipalIntegrand (I := I) (M := M) g r s S T α y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  have h := tensorCovDerivPointwiseInner_chart_eq (I := I) (M := M)
    g r s S T α hy
  change covLowerOrderIntegrand (I := I) (M := M) g r s S T α y =
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) -
      covPrincipalIntegrand (I := I) (M := M) g r s S T α y
  rw [h]
  ring

omit [CompleteSpace E] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covLowerOrderIntegrand_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covLowerOrderIntegrand (I := I) (M := M) g r s S T α y =
      covLowerOrderIntegrand (I := I) (M := M) g r s T S α y := by
  classical
  rw [covLowerOrderIntegrand_def, covLowerOrderIntegrand_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [covChartMetricGram_symm (I := I) (M := M) g r s α Q P y]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [show chartInvGramEuclid (I := I) g α l k y =
      chartInvGramEuclid (I := I) g α k l y from ?_]
  · ring
  · rw [chartInvGramEuclid_def, chartInvGramEuclid_def, chartInvGramOnE_def,
      chartInvGramOnE_def]
    have hHerm : (chartInvGramMatrix (I := I) g α
        ((extChartAt I α).symm (toEuclidean.symm y))).IsHermitian := by
      unfold chartInvGramMatrix
      exact (chartGramMatrix_isHermitian (I := I) g α
        ((extChartAt I α).symm (toEuclidean.symm y))).inv
    have hsymm := hHerm.apply k l
    rw [star_trivial] at hsymm
    exact hsymm

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
