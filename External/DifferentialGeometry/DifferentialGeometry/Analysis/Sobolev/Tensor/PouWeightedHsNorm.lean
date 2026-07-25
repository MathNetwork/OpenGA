import DifferentialGeometry.Analysis.Sobolev.Tensor.PouWeightedNorm
import DifferentialGeometry.Analysis.Sobolev.Approximation.SmoothDensity


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def tensorPouSobolevHsNorm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) : ℝ≥0∞ :=
  (∑' α : M,
    ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      ∑ j ∈ Finset.range (2 * k + 1),
        ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
          ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s T α
                          IJ.1 IJ.2
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
            ∂(volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) ^
    (1 / 2 : ℝ)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorPouSobolevHsNorm_eq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevHsNorm (I := I) (M := M) g k T =
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α
                              IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) ^ (1 / 2 : ℝ) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorPouSobolevHsNorm_nonneg
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    0 ≤ tensorPouSobolevHsNorm (I := I) (M := M) g k T :=
  zero_le _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorChartComponentRaw_comp_euclid_zero_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (tensorChartComponentRaw (I := I) (M := M) g r s
        (0 : SmoothCcTensor g r s) α Idx Jdx
      ∘ (extChartAt I α).symm
      ∘ (toEuclidean (E := E)).symm) =
      (fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => (0 : ℝ)) := by
  funext y
  have hM : tensorChartComponentRaw (I := I) (M := M) g r s
      (0 : SmoothCcTensor g r s) α Idx Jdx
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
    have hraw_comp :
        (tensorChartComponentRaw (I := I) (M := M) g r s
            (0 : SmoothCcTensor g r s) α Idx Jdx
          ∘ (extChartAt I α).symm) =
          (fun _ : E => (0 : ℝ)) := by
      funext x
      change tensorChartComponentRaw (I := I) (M := M) g r s
          (0 : SmoothCcTensor g r s) α Idx Jdx ((extChartAt I α).symm x) = 0
      classical
      have h0 : (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ
              ((extChartAt I α).symm x)
              ((0 : SmoothCcTensor g r s).toSection ((extChartAt I α).symm x))
              = 0 := by
        have hsec : (0 : SmoothCcTensor g r s).toSection
            ((extChartAt I α).symm x) = 0 := by rfl
        rw [hsec]
        exact map_zero _
      unfold tensorChartComponentRaw
      change tensorChartComponentProjection (E := E) r s Idx Jdx
          (tensorTrivProj (I := I) (M := M) g r s
            (0 : SmoothCcTensor g r s) α ((extChartAt I α).symm x)) = 0
      unfold tensorTrivProj
      rw [h0]
      exact map_zero _
    have := congrFun hraw_comp ((toEuclidean (E := E)).symm y)
    exact this
  exact hM

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorPouSobolevHsNorm_zero_section
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ) :
    tensorPouSobolevHsNorm (I := I) (M := M) g k
        (0 : SmoothCcTensor g r s) = 0 := by
  classical
  rw [tensorPouSobolevHsNorm_eq]
  have htsum :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s
                              (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) = 0 := by
    have hpt : ∀ α : M,
        (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s
                              (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) = 0 := by
      intro α
      refine Finset.sum_eq_zero ?_
      intro IJ _
      refine Finset.sum_eq_zero ?_
      intro j _
      refine Finset.sum_eq_zero ?_
      intro basisIdx _
      have hraw := tensorChartComponentRaw_comp_euclid_zero_section
        (I := I) (M := M) g r s α IJ.1 IJ.2
      have hiter : iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s
              (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
            ∘ (extChartAt I α).symm
            ∘ (toEuclidean (E := E)).symm) = 0 := by
        rw [hraw]
        exact iteratedFDeriv_fun_zero
      have hintegrand_zero :
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            ENNReal.ofReal
              (((chartAtlasPOU I M α : M → ℝ)
                  ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                |(iteratedFDeriv ℝ j
                      (tensorChartComponentRaw (I := I) (M := M) g r s
                          (0 : SmoothCcTensor g r s) α IJ.1 IJ.2
                        ∘ (extChartAt I α).symm
                        ∘ (toEuclidean (E := E)).symm)
                      y)
                    (fun i => EuclideanSpace.basisFun
                      (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)) =
            (fun _ => 0) := by
        funext y
        rw [hiter]
        simp
      rw [hintegrand_zero]
      simp
    rw [tsum_congr hpt]
    exact tsum_zero
  rw [htsum]
  exact ENNReal.zero_rpow_of_pos (by norm_num)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorPouSobolevHsNorm_le_succ
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevHsNorm (I := I) (M := M) g k T ≤
      tensorPouSobolevHsNorm (I := I) (M := M) g (k + 1) T := by
  classical
  rw [tensorPouSobolevHsNorm_eq, tensorPouSobolevHsNorm_eq]
  have hrange : Finset.range (2 * k + 1) ⊆ Finset.range (2 * (k + 1) + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hper_chart : ∀ α : M,
      (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * k + 1),
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T α
                            IJ.1 IJ.2
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ
                  (Fin (Module.finrank ℝ E))))) ≤
      (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * (k + 1) + 1),
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s T α
                            IJ.1 IJ.2
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ
                  (Fin (Module.finrank ℝ E))))) := by
    intro α
    refine Finset.sum_le_sum ?_
    intro IJ _
    exact Finset.sum_le_sum_of_subset_of_nonneg hrange
      (by intro j _ _; exact zero_le _)
  have htsum_le :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α
                              IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) ≤
        (∑' α : M,
          ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * (k + 1) + 1),
              ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      |(iteratedFDeriv ℝ j
                            (tensorChartComponentRaw (I := I) (M := M) g r s T α
                                IJ.1 IJ.2
                              ∘ (extChartAt I α).symm
                              ∘ (toEuclidean (E := E)).symm)
                            y)
                          (fun i => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                  ∂(volume :
                    Measure (EuclideanSpace ℝ
                      (Fin (Module.finrank ℝ E))))) := by
    exact ENNReal.tsum_le_tsum hper_chart
  exact ENNReal.rpow_le_rpow htsum_le (by norm_num)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorChartComponentRaw_comp_euclid_smul_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (tensorChartComponentRaw (I := I) (M := M) g r s (c • T) α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) =
      c • (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) := by
  funext y
  have h := tensorChartComponentRaw_smul (I := I) (M := M) g r s c T α Idx Jdx
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
  change tensorChartComponentRaw (I := I) (M := M) g r s (c • T) α Idx Jdx
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
    c • (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
  exact h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorChartComponentRawEuclidPull_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have h_raw_smoothOn : ContMDiffOn I (𝓘(ℝ, ℝ)) ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)
      ((chartAt H α).source) :=
    tensorChartComponentRaw_contMDiffOn_chart_source
      (I := I) (M := M) g r s T α Idx Jdx
  have h_raw_pull_contDiffOn :
      ContDiffOn ℝ ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm)
        (extChartAt I α).target := by
    have h_extSymm : ContMDiffOn 𝓘(ℝ, E) I ∞
        ((extChartAt I α).symm : E → M) (extChartAt I α).target :=
      contMDiffOn_extChartAt_symm α
    have h_comp_mdiff : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, ℝ)) ∞
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm)
        (extChartAt I α).target := by
      refine h_raw_smoothOn.comp h_extSymm ?_
      intro y hy
      change (extChartAt I α).symm y ∈ (chartAt H α).source
      rw [← extChartAt_source (I := I)]
      exact (extChartAt I α).map_target hy
    exact h_comp_mdiff.contDiffOn
  have h_toEucl_symm_smooth :
      ContDiff ℝ ∞ ((toEuclidean (E := E)).symm) :=
    ContinuousLinearEquiv.contDiff _
  have h_maps : Set.MapsTo ((toEuclidean (E := E)).symm)
      (chartTargetEuclid (I := I) (M := M) α)
      (extChartAt I α).target := by
    intro y hy
    rcases hy with ⟨z, hz_tgt, hz_eq⟩
    have h_eq : (toEuclidean (E := E)).symm y = z := by
      rw [← hz_eq]; exact (toEuclidean (E := E)).symm_apply_apply z
    rw [h_eq]; exact hz_tgt
  exact h_raw_pull_contDiffOn.comp
    h_toEucl_symm_smooth.contDiffOn h_maps

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem iteratedFDeriv_basisEval_smul_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (iteratedFDeriv ℝ j
        (tensorChartComponentRaw (I := I) (M := M) g r s (c • T) α Idx Jdx
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) y)
      (fun i => EuclideanSpace.basisFun
        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) =
    c • (iteratedFDeriv ℝ j
        (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) y)
      (fun i => EuclideanSpace.basisFun
        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) := by
  classical
  have hfun : (tensorChartComponentRaw (I := I) (M := M) g r s (c • T) α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) =
      c • (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) :=
    tensorChartComponentRaw_comp_euclid_smul_eq
      (I := I) (M := M) g r s c T α Idx Jdx
  rw [hfun]
  have h_cdAt : ContDiffAt ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) y := by
    have h_cdOn := tensorChartComponentRawEuclidPull_contDiffOn
      (I := I) (M := M) g r s T α Idx Jdx
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    exact h_cdOn.contDiffAt (h_open.mem_nhds hy)
  have h_cdAt_n : ContDiffAt ℝ j
      (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) y :=
    h_cdAt.of_le (by exact_mod_cast le_top)
  rw [iteratedFDeriv_const_smul_apply h_cdAt_n]
  exact ContinuousMultilinearMap.smul_apply _ _ _

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem tensorPouSobolevHsNorm_smul
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (c : ℝ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevHsNorm (I := I) (M := M) g k (c • T) =
      ENNReal.ofReal |c| *
        tensorPouSobolevHsNorm (I := I) (M := M) g k T := by
  classical
  rw [tensorPouSobolevHsNorm_eq, tensorPouSobolevHsNorm_eq]
  have h_inner_eq : ∀ α : M,
      (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
        ∑ j ∈ Finset.range (2 * k + 1),
          ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
            ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
              ENNReal.ofReal
                (((chartAtlasPOU I M α : M → ℝ)
                    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                  |(iteratedFDeriv ℝ j
                        (tensorChartComponentRaw (I := I) (M := M) g r s
                            (c • T) α IJ.1 IJ.2
                          ∘ (extChartAt I α).symm
                          ∘ (toEuclidean (E := E)).symm)
                        y)
                      (fun i => EuclideanSpace.basisFun
                        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
              ∂(volume :
                Measure (EuclideanSpace ℝ
                  (Fin (Module.finrank ℝ E))))) =
      ENNReal.ofReal (c ^ 2) *
        (∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α
                              IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) := by
    intro α
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro IJ _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro basisIdx _
    rw [← MeasureTheory.lintegral_const_mul']
    swap
    · exact ENNReal.ofReal_ne_top
    refine MeasureTheory.setLIntegral_congr_fun
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet ?_
    intro y hy
    change ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s
                    (c • T) α IJ.1 IJ.2
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) =
      ENNReal.ofReal (c ^ 2) *
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α
                      IJ.1 IJ.2
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm) y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
    have hbe := iteratedFDeriv_basisEval_smul_eq
      (I := I) (M := M) g r s c T α IJ.1 IJ.2 j basisIdx hy
    have hPOU_nn : 0 ≤ (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) :=
      (chartAtlasPOU I M).nonneg α _
    have hcsq_nn : (0 : ℝ) ≤ c ^ 2 := sq_nonneg _
    have hcalc :
        ((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s
                    (c • T) α IJ.1 IJ.2
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm) y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 =
        (c ^ 2) *
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α
                      IJ.1 IJ.2
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm) y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) := by
      rw [hbe]
      have hsmul_eq : (c • (iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                ∘ (extChartAt I α).symm
                ∘ (toEuclidean (E := E)).symm) y)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) : ℝ) =
          c * (iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α IJ.1 IJ.2
                ∘ (extChartAt I α).symm
                ∘ (toEuclidean (E := E)).symm) y)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) := rfl
      rw [hsmul_eq, abs_mul, mul_pow, sq_abs]
      ring
    rw [hcalc, ENNReal.ofReal_mul hcsq_nn]
  have htsum_eq :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s
                              (c • T) α IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) =
      ENNReal.ofReal (c ^ 2) *
        (∑' α : M,
          ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
            ∑ j ∈ Finset.range (2 * k + 1),
              ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
                ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                  ENNReal.ofReal
                    (((chartAtlasPOU I M α : M → ℝ)
                        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                      |(iteratedFDeriv ℝ j
                            (tensorChartComponentRaw (I := I) (M := M) g r s T α
                                IJ.1 IJ.2
                              ∘ (extChartAt I α).symm
                              ∘ (toEuclidean (E := E)).symm)
                            y)
                          (fun i => EuclideanSpace.basisFun
                            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                  ∂(volume :
                    Measure (EuclideanSpace ℝ
                      (Fin (Module.finrank ℝ E))))) := by
    rw [tsum_congr h_inner_eq]
    rw [ENNReal.tsum_mul_left]
  rw [htsum_eq]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
  congr 1
  rw [show (c ^ 2 : ℝ) = |c| ^ 2 from (sq_abs c).symm]
  rw [ENNReal.ofReal_pow (abs_nonneg _)]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem tensorPouSobolevHsNorm_neg
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevHsNorm (I := I) (M := M) g k (-T) =
      tensorPouSobolevHsNorm (I := I) (M := M) g k T := by
  have hsmul := tensorPouSobolevHsNorm_smul (I := I) (M := M) g k (-1 : ℝ) T
  rw [neg_one_smul] at hsmul
  rw [hsmul]
  have h_abs : |(-1 : ℝ)| = 1 := by simp
  rw [h_abs, ENNReal.ofReal_one, one_mul]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorPouSobolevHsNorm_inner_integral_lt_top'
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E)) :
    (∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
        ENNReal.ofReal
          (((chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) < ⊤ := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartImagePOUTsupport (I := I) (M := M) α with hK_def
  have hK_compact : IsCompact K :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hK_sub : K ⊆ chartTargetEuclid (I := I) (M := M) α :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  set f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ≥0∞ :=
    fun y =>
      ENNReal.ofReal
        (((chartAtlasPOU I M α : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm)
                y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) with hf_def
  have hf_zero_off_K : ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
      y ∉ K → f y = 0 := by
    intro y hy_target hy_off
    have hpush_zero :
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
          α (fun _ : M => (1 : ℝ)) y = 0 :=
      chartPushed_eq_zero_off_chartImagePOUTsupport (I := I) (M := M)
        α (fun _ => 1) hy_target hy_off
    have hpush_unfold :
        chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
            α (fun _ : M => (1 : ℝ)) y =
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : M → ℝ)
            ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) := by
      simp [chartPushed]
    have hPOU_y : (chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) = 0 := by
      rw [← hpush_unfold]; exact hpush_zero
    change ENNReal.ofReal (((chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) * _) = 0
    rw [hPOU_y, zero_mul, ENNReal.ofReal_zero]
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hT_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
  have hsplit :
      (∫⁻ y in chartTargetEuclid (I := I) (M := M) α, f y
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))) =
      ∫⁻ y in K, f y
        ∂(volume :
          Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
    rw [← MeasureTheory.lintegral_indicator hT_meas,
        ← MeasureTheory.lintegral_indicator hK_meas]
    refine MeasureTheory.lintegral_congr (fun y => ?_)
    by_cases hyK : y ∈ K
    · have hyT : y ∈ chartTargetEuclid (I := I) (M := M) α := hK_sub hyK
      simp [Set.indicator_of_mem, hyK, hyT]
    · by_cases hyT : y ∈ chartTargetEuclid (I := I) (M := M) α
      · have hf0 : f y = 0 := hf_zero_off_K y hyT hyK
        rw [Set.indicator_of_mem hyT, Set.indicator_of_notMem hyK, hf0]
      · simp [Set.indicator_of_notMem, hyK, hyT]
  rw [hsplit]
  have hK_vol : (volume :
      Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) K < ⊤ :=
    hK_compact.measure_lt_top
  set ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ := fun y =>
    ((chartAtlasPOU I M α : M → ℝ)
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
      |(iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm)
            y)
          (fun i => EuclideanSpace.basisFun
            (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2 with hψ_def
  have hψ_contOn :
      ContinuousOn ψ (chartTargetEuclid (I := I) (M := M) α) := by
    have hPOU_smooth :
        ContMDiff I (𝓘(ℝ, ℝ)) ∞
          (fun x : M => (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x) :=
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯).contMDiff
    have hPOU_pull_cont :
        ContinuousOn (fun y : EuclideanSpace ℝ
              (Fin (Module.finrank ℝ E)) =>
            (chartAtlasPOU I M α : M → ℝ)
              ((extChartAt I α).symm
                ((toEuclidean (E := E)).symm y)))
          (chartTargetEuclid (I := I) (M := M) α) := by
      have hPOU_cont :
          Continuous fun x : M => (chartAtlasPOU I M α : M → ℝ) x :=
        hPOU_smooth.continuous
      have hSymmCont : ContinuousOn ((extChartAt I α).symm)
          (extChartAt I α).target :=
        continuousOn_extChartAt_symm α
      have h_toEucl_cont : Continuous
          ((toEuclidean (E := E)).symm : _ → _) :=
        (toEuclidean (E := E)).symm.continuous
      have h_inner : ContinuousOn
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            (extChartAt I α).symm ((toEuclidean (E := E)).symm y))
          (chartTargetEuclid (I := I) (M := M) α) := by
        refine hSymmCont.comp h_toEucl_cont.continuousOn ?_
        intro y hy
        unfold chartTargetEuclid at hy
        obtain ⟨z, hz_tgt, hz_eq⟩ := hy
        rw [← hz_eq]
        change (toEuclidean (E := E)).symm
            ((toEuclidean (E := E)) z) ∈ (extChartAt I α).target
        rw [(toEuclidean (E := E)).symm_apply_apply]
        exact hz_tgt
      exact hPOU_cont.comp_continuousOn' h_inner
    have h_iter_contOn : ContinuousOn
        (iteratedFDeriv ℝ j
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm
            ∘ (toEuclidean (E := E)).symm))
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
        chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_cdOn :
          ContDiffOn ℝ ∞
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm)
            (chartTargetEuclid (I := I) (M := M) α) :=
        tensorChartComponentRawEuclidPull_contDiffOn
          (I := I) (M := M) g r s T α Idx Jdx
      intro y hy
      have h_cd : ContDiffAt ℝ ∞
          (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
            ∘ (extChartAt I α).symm
            ∘ (toEuclidean (E := E)).symm) y :=
        h_cdOn.contDiffAt (h_open.mem_nhds hy)
      have h_cont_iter : ContinuousAt
          (iteratedFDeriv ℝ j
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
              ∘ (extChartAt I α).symm
              ∘ (toEuclidean (E := E)).symm)) y :=
        h_cd.continuousAt_iteratedFDeriv (k := j) (by exact_mod_cast le_top)
      exact h_cont_iter.continuousWithinAt
    have h_eval_contOn : ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (iteratedFDeriv ℝ j
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                ∘ (extChartAt I α).symm
                ∘ (toEuclidean (E := E)).symm)
              y)
            (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)))
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_apply : Continuous
          fun A : ContinuousMultilinearMap ℝ
              (fun _ : Fin j => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ℝ =>
            A (fun i => EuclideanSpace.basisFun
              (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) :=
        continuous_eval_const _
      exact h_apply.comp_continuousOn h_iter_contOn
    have h_abs_sq_contOn : ContinuousOn
        (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          |(iteratedFDeriv ℝ j
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                  ∘ (extChartAt I α).symm
                  ∘ (toEuclidean (E := E)).symm)
                y)
              (fun i => EuclideanSpace.basisFun
                (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
        (chartTargetEuclid (I := I) (M := M) α) := by
      have h_abs : ContinuousOn
          (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            |(iteratedFDeriv ℝ j
                  (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx
                    ∘ (extChartAt I α).symm
                    ∘ (toEuclidean (E := E)).symm)
                  y)
                (fun i => EuclideanSpace.basisFun
                  (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))|)
          (chartTargetEuclid (I := I) (M := M) α) :=
        h_eval_contOn.abs
      exact h_abs.pow 2
    exact hPOU_pull_cont.mul h_abs_sq_contOn
  have hψ_contOn_K : ContinuousOn ψ K := hψ_contOn.mono hK_sub
  have hψ_bdd : ∃ M : ℝ, ∀ y ∈ K, ψ y ≤ M := by
    obtain ⟨M, hM⟩ := (hK_compact.image_of_continuousOn hψ_contOn_K).bddAbove
    refine ⟨M, fun y hy => ?_⟩
    exact hM ⟨y, hy, rfl⟩
  obtain ⟨B, hB⟩ := hψ_bdd
  refine MeasureTheory.setLIntegral_lt_top_of_le_nnreal hK_vol.ne ?_
  refine ⟨B.toNNReal, fun y hy => ?_⟩
  rw [hf_def]
  refine ENNReal.ofReal_le_of_le_toReal ?_
  change ψ y ≤ (B.toNNReal : ℝ≥0∞).toReal
  rw [ENNReal.coe_toReal, Real.coe_toNNReal']
  exact (hB y hy).trans (le_max_left _ _)

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorPouSobolevHsNorm_lt_top
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevHsNorm (I := I) (M := M) g k T < ⊤ := by
  classical
  rw [tensorPouSobolevHsNorm_eq]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have htsum_eq :
      (∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α
                              IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E))))) =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α
                              IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E)))) := by
    refine tsum_eq_sum ?_
    intro α hα
    have hPOU_zero : ∀ x : M, (chartAtlasPOU I M α : M → ℝ) x = 0 :=
      fun x => chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
    refine Finset.sum_eq_zero ?_
    intro IJ _
    refine Finset.sum_eq_zero ?_
    intro j _
    refine Finset.sum_eq_zero ?_
    intro basisIdx _
    have h_integrand_zero :
        ∀ y ∈ chartTargetEuclid (I := I) (M := M) α,
          ENNReal.ofReal
            (((chartAtlasPOU I M α : M → ℝ)
                ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
              |(iteratedFDeriv ℝ j
                    (tensorChartComponentRaw (I := I) (M := M) g r s T α
                        IJ.1 IJ.2
                      ∘ (extChartAt I α).symm
                      ∘ (toEuclidean (E := E)).symm)
                    y)
                  (fun i => EuclideanSpace.basisFun
                    (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2) = 0 := by
      intro y _
      rw [hPOU_zero, zero_mul, ENNReal.ofReal_zero]
    rw [MeasureTheory.setLIntegral_congr_fun
      (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet
      h_integrand_zero]
    simp
  rw [htsum_eq]
  refine (ENNReal.sum_lt_top.mpr ?_).ne
  intro α _
  refine ENNReal.sum_lt_top.mpr ?_
  intro IJ _
  refine ENNReal.sum_lt_top.mpr ?_
  intro j _
  refine ENNReal.sum_lt_top.mpr ?_
  intro basisIdx _
  exact tensorPouSobolevHsNorm_inner_integral_lt_top'
    (I := I) (M := M) g r s T α IJ.1 IJ.2 j basisIdx

noncomputable def tensorPouSobolevHsNormSq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) : ℝ≥0∞ :=
  tensorPouSobolevHsNorm (I := I) (M := M) g k T ^ 2

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorPouSobolevHsNormSq_eq_inner_sum
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevHsNormSq (I := I) (M := M) g k T =
      ∑' α : M,
        ∑ IJ : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ basisIdx : Fin j → Fin (Module.finrank ℝ E),
              ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
                ENNReal.ofReal
                  (((chartAtlasPOU I M α : M → ℝ)
                      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
                    |(iteratedFDeriv ℝ j
                          (tensorChartComponentRaw (I := I) (M := M) g r s T α
                              IJ.1 IJ.2
                            ∘ (extChartAt I α).symm
                            ∘ (toEuclidean (E := E)).symm)
                          y)
                        (fun i => EuclideanSpace.basisFun
                          (Fin (Module.finrank ℝ E)) ℝ (basisIdx i))| ^ 2)
                ∂(volume :
                  Measure (EuclideanSpace ℝ
                    (Fin (Module.finrank ℝ E)))) := by
  classical
  unfold tensorPouSobolevHsNormSq
  rw [tensorPouSobolevHsNorm_eq]
  rw [← ENNReal.rpow_natCast (_ ^ (1/2 : ℝ)) 2,
      ← ENNReal.rpow_mul]
  simp

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorPouSobolevHsNormSq_lt_top
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    tensorPouSobolevHsNormSq (I := I) (M := M) g k T < ⊤ := by
  unfold tensorPouSobolevHsNormSq
  exact ENNReal.pow_lt_top
    (tensorPouSobolevHsNorm_lt_top (I := I) (M := M) g k T)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma tensorChartComponentRaw_comp_euclid_add_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T₁ T₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    (tensorChartComponentRaw (I := I) (M := M) g r s (T₁ + T₂) α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) =
      (tensorChartComponentRaw (I := I) (M := M) g r s T₁ α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) +
      (tensorChartComponentRaw (I := I) (M := M) g r s T₂ α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) := by
  funext y
  have h := tensorChartComponentRaw_add (I := I) (M := M) g r s T₁ T₂ α Idx Jdx
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
  exact h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
theorem iteratedFDeriv_basisEval_add_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T₁ T₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (j : ℕ) (basisIdx : Fin j → Fin (Module.finrank ℝ E))
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (iteratedFDeriv ℝ j
        (tensorChartComponentRaw (I := I) (M := M) g r s (T₁ + T₂) α Idx Jdx
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) y)
      (fun i => EuclideanSpace.basisFun
        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) =
    (iteratedFDeriv ℝ j
        (tensorChartComponentRaw (I := I) (M := M) g r s T₁ α Idx Jdx
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) y)
      (fun i => EuclideanSpace.basisFun
        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) +
    (iteratedFDeriv ℝ j
        (tensorChartComponentRaw (I := I) (M := M) g r s T₂ α Idx Jdx
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) y)
      (fun i => EuclideanSpace.basisFun
        (Fin (Module.finrank ℝ E)) ℝ (basisIdx i)) := by
  classical
  have hfun :
      (tensorChartComponentRaw (I := I) (M := M) g r s (T₁ + T₂) α Idx Jdx
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) =
        (tensorChartComponentRaw (I := I) (M := M) g r s T₁ α Idx Jdx
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) +
        (tensorChartComponentRaw (I := I) (M := M) g r s T₂ α Idx Jdx
          ∘ (extChartAt I α).symm
          ∘ (toEuclidean (E := E)).symm) :=
    tensorChartComponentRaw_comp_euclid_add_eq
      (I := I) (M := M) g r s T₁ T₂ α Idx Jdx
  rw [hfun]
  have h_cdAt₁ : ContDiffAt ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T₁ α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) y := by
    have h_cdOn := tensorChartComponentRawEuclidPull_contDiffOn
      (I := I) (M := M) g r s T₁ α Idx Jdx
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    exact h_cdOn.contDiffAt (h_open.mem_nhds hy)
  have h_cdAt₂ : ContDiffAt ℝ ∞
      (tensorChartComponentRaw (I := I) (M := M) g r s T₂ α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) y := by
    have h_cdOn := tensorChartComponentRawEuclidPull_contDiffOn
      (I := I) (M := M) g r s T₂ α Idx Jdx
    have h_open : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
      chartTargetEuclid_isOpen (I := I) (M := M) α
    exact h_cdOn.contDiffAt (h_open.mem_nhds hy)
  have h_cdAt₁_n : ContDiffAt ℝ j
      (tensorChartComponentRaw (I := I) (M := M) g r s T₁ α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) y :=
    h_cdAt₁.of_le (by exact_mod_cast le_top)
  have h_cdAt₂_n : ContDiffAt ℝ j
      (tensorChartComponentRaw (I := I) (M := M) g r s T₂ α Idx Jdx
        ∘ (extChartAt I α).symm
        ∘ (toEuclidean (E := E)).symm) y :=
    h_cdAt₂.of_le (by exact_mod_cast le_top)
  rw [iteratedFDeriv_add_apply h_cdAt₁_n h_cdAt₂_n]
  rfl

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
