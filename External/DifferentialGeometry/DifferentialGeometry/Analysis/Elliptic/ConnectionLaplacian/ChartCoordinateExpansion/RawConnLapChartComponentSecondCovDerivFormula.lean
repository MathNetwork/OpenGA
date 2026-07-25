import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.RawConnLapChartComponentFrameTrace
import DifferentialGeometry.Geometry.Connection.ChartFrameNormGlobalSmoothCoordBasisExpansion
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.SecondCovDerivExpansion.ChartProjectionSecondCovDerivViaSkExt
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovDeriv.ComponentEuclidSkExtExpansion
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Defs


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private noncomputable def principalSecondDerivSum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
      weightedInvGramEuclid (I := I) (M := M) g α k l y *
        euclidPartial (E := E) l
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
private lemma principalSecondDerivSum_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (principalSecondDerivSum (I := I) (M := M) g r s α T₀ Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hk : ∀ k : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
        (chartTargetEuclid (I := I) (M := M) α) := fun k =>
    euclidPartial_chartPushedRaw_contDiffOn (I := I) (M := M) g r s T₀ α k Idx Jdx
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    chartTargetEuclid_isOpen (I := I) (M := M) α
  have hkl : ∀ k l : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (euclidPartial (E := E) l
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))))
        (chartTargetEuclid (I := I) (M := M) α) := by
    intro k l
    have hu := hk k
    have hsucc : ContDiffOn ℝ ((∞ : WithTop ℕ∞) + 1)
        (euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
        (chartTargetEuclid (I := I) (M := M) α) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from rfl]; exact hu
    have hfw : ContDiffOn ℝ ∞
        (fderivWithin ℝ
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
          (chartTargetEuclid (I := I) (M := M) α))
        (chartTargetEuclid (I := I) (M := M) α) :=
      ((contDiffOn_succ_iff_fderivWithin hopen.uniqueDiffOn).mp hsucc).2.2
    have hfderiv : ContDiffOn ℝ ∞
        (fun z => fderiv ℝ
          (euclidPartial (E := E) k
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) z)
        (chartTargetEuclid (I := I) (M := M) α) := by
      refine hfw.congr (fun z hz => ?_)
      exact (fderivWithin_of_isOpen (f :=
        euclidPartial (E := E) k
          (chartPushedRaw I α
            (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
        (𝕜 := ℝ) hopen hz).symm
    have hcomp : ContDiffOn ℝ ∞
        ((fun L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] ℝ =>
            L (EuclideanSpace.single l 1)) ∘
          (fun z => fderiv ℝ
            (euclidPartial (E := E) k
              (chartPushedRaw I α
                (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) z))
        (chartTargetEuclid (I := I) (M := M) α) :=
      (ContinuousLinearMap.apply ℝ ℝ
        (EuclideanSpace.single l 1)).contDiff.comp_contDiffOn hfderiv
    refine hcomp.congr (fun z _ => ?_)
    rfl
  have hsum_pair : ∀ k l : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun y =>
          weightedInvGramEuclid (I := I) (M := M) g α k l y *
            euclidPartial (E := E) l
              (euclidPartial (E := E) k
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y)
        (chartTargetEuclid (I := I) (M := M) α) := fun k l =>
    (weightedInvGramEuclid_contDiffOn (I := I) (M := M) g α k l).mul (hkl k l)
  have hsum_inner : ∀ k : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞
        (fun y =>
          ∑ l : Fin (Module.finrank ℝ E),
            weightedInvGramEuclid (I := I) (M := M) g α k l y *
              euclidPartial (E := E) l
                (euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx))) y)
        (chartTargetEuclid (I := I) (M := M) α) := fun k =>
    ContDiffOn.sum (fun l _ => hsum_pair k l)
  exact ContDiffOn.sum (fun k _ => hsum_inner k)

private noncomputable def chartPushed_rawConnLapComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  chartPushedRaw I α
    (tensorChartComponentRaw (I := I) (M := M) g r s
      (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx)

omit [CompactSpace M] [I.Boundaryless] in
private lemma chartPushed_rawConnLapComponent_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (chartPushed_rawConnLapComponent (I := I) (M := M) g r s α T₀ Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  chartPushedRaw_tensorChartComponentRaw_contDiffOn (I := I) (M := M) g r s
    (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx

private noncomputable def lowerOrderCorrection
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    chartPushed_rawConnLapComponent (I := I) (M := M) g r s α T₀ Idx Jdx y -
      principalSecondDerivSum (I := I) (M := M) g r s α T₀ Idx Jdx y

omit [CompactSpace M] in
private lemma lowerOrderCorrection_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (lowerOrderCorrection (I := I) (M := M) g r s α T₀ Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (chartPushed_rawConnLapComponent_contDiffOn (I := I) (M := M) g r s α T₀
    Idx Jdx).sub
    (principalSecondDerivSum_contDiffOn (I := I) (M := M) g r s α T₀ Idx Jdx)

omit [CompactSpace M] [I.Boundaryless] in
private lemma chartPushed_rawConnLapComponent_eq_principal_add_LO
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    chartPushed_rawConnLapComponent (I := I) (M := M) g r s α T₀ Idx Jdx y =
      principalSecondDerivSum (I := I) (M := M) g r s α T₀ Idx Jdx y +
        lowerOrderCorrection (I := I) (M := M) g r s α T₀ Idx Jdx y := by
  unfold lowerOrderCorrection
  ring

omit [CompactSpace M] [I.Boundaryless] in
private lemma chartPushed_rawConnLapComponent_apply_of_good
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartPushed_rawConnLapComponent (I := I) (M := M) g r s α T₀ Idx Jdx
        ((toEuclidean (E := E)) ((extChartAt I α) b)) =
      tensorChartComponentRaw (I := I) (M := M) g r s
        (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b := by
  classical
  unfold chartPushed_rawConnLapComponent
  have hb_src : b ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hb
  have hb_tgt : (extChartAt I α) b ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source hb_src
  have hy_chart : (toEuclidean (E := E)) ((extChartAt I α) b) ∈
      chartTargetEuclid (I := I) (M := M) α :=
    ⟨(extChartAt I α) b, hb_tgt, rfl⟩
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy_chart]
  have hsymm_te :
      (toEuclidean (E := E)).symm
        ((toEuclidean (E := E)) ((extChartAt I α) b)) =
        (extChartAt I α) b :=
    (toEuclidean (E := E)).symm_apply_apply _
  have hleft_inv : (extChartAt I α).symm ((extChartAt I α) b) = b :=
    (extChartAt I α).left_inv hb_src
  rw [hsymm_te, hleft_inv]

omit [CompactSpace M] in
theorem tensorChartComponentRaw_rawTensorConnLap_eq_chart_α_coord_formula
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T₀ : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b₀ : M}
    (hb₀ : b₀ ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
      chartLeviCivitaGoodSet (I := I) α) :
    ∃ U : Set M, IsOpen U ∧ b₀ ∈ U ∧
      U ⊆ chartLeviCivitaGoodSet (I := I) α ∧
    ∃ (Coeff_2 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
                  EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
    ∃ (Coeff_LO : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ),
      (∀ k l, ContDiffOn ℝ ∞ (Coeff_2 k l)
        (chartTargetEuclid (I := I) (M := M) α)) ∧
      (ContDiffOn ℝ ∞ Coeff_LO (chartTargetEuclid (I := I) (M := M) α)) ∧
      ∀ b ∈ U,
        tensorChartComponentRaw (I := I) (M := M) g r s
          (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
          (∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
            Coeff_2 k l ((toEuclidean (E := E)) ((extChartAt I α) b)) *
              euclidPartial (E := E) l
                (euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M) g r s T₀ α Idx Jdx)))
                ((toEuclidean (E := E)) ((extChartAt I α) b))) +
          Coeff_LO ((toEuclidean (E := E)) ((extChartAt I α) b)) := by
  classical
  refine ⟨chartLeviCivitaGoodSet (I := I) α,
    chartLeviCivitaGoodSet_isOpen (I := I) α, hb₀.2, Set.Subset.rfl, ?_⟩
  refine ⟨fun k l => weightedInvGramEuclid (I := I) (M := M) g α k l, ?_, ?_, ?_, ?_⟩
  · exact lowerOrderCorrection (I := I) (M := M) g r s α T₀ Idx Jdx
  · intro k l
    exact weightedInvGramEuclid_contDiffOn (I := I) (M := M) g α k l
  · exact lowerOrderCorrection_contDiffOn (I := I) (M := M) g r s α T₀ Idx Jdx
  · intro b hb
    set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
      (toEuclidean (E := E)) ((extChartAt I α) b) with hy_def
    have hLHS_eq :
        tensorChartComponentRaw (I := I) (M := M) g r s
            (rawTensorConnLapSmooth (I := I) g r s T₀) α Idx Jdx b =
          chartPushed_rawConnLapComponent (I := I) (M := M) g r s α T₀ Idx Jdx y :=
      (chartPushed_rawConnLapComponent_apply_of_good
        (I := I) (M := M) g r s α T₀ Idx Jdx hb).symm
    rw [hLHS_eq]
    rw [chartPushed_rawConnLapComponent_eq_principal_add_LO
        (I := I) (M := M) g r s α T₀ Idx Jdx y]
    rfl

end Connection
end Integral
end DifferentialGeometry

end
