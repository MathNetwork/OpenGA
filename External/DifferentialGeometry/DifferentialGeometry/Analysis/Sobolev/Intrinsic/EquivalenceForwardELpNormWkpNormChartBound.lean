import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Equivalence
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Lp
import DifferentialGeometry.Analysis.Sobolev.Approximation.ContMDiffDense
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Sobolev.Manifold.EmbeddingSubcritical
import DifferentialGeometry.Analysis.Sobolev.Manifold.MorreyManifold
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.IntegrationByParts
import DifferentialGeometry.Geometry.Operator.Laplacian
import DifferentialGeometry.Analysis.Integration.Measure.Family
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace EquivalenceFull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Intrinsic
open DifferentialGeometry.Analysis.Sobolev.IntrinsicLp

theorem eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, Measurable u →
        eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) ≤
          ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) g 1 p u := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M)
    with hS_def
  set ρ := DifferentialGeometry.Integral.Measure.chartAtlasPOU I M with hρ_def
  have h_bridge_α : ∀ α : M, ∃ C_α : ℝ, 0 < C_α ∧
      ∀ {u : M → ℝ}, Measurable u → tsupport u ⊆ tsupport (ρ α : M → ℝ) →
        eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g ρ)
          ≤ ENNReal.ofReal C_α *
              eLpNorm
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u) p
                ((volume :
                  Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                  (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                    (I := I) (M := M) α)) := by
    intro α
    set Kα : Set M := tsupport (ρ α : M → ℝ) with hKα_def
    have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
    have hKα_sub : Kα ⊆ (chartAt H α).source :=
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
    obtain ⟨C_α, hC_α_pos, hbound⟩ :=
      DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
        (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
    exact ⟨C_α, hC_α_pos, hbound⟩
  set Cα : M → ℝ := fun α => Classical.choose (h_bridge_α α) with hCα_def
  have hCα_pos : ∀ α : M, 0 < Cα α := fun α => (Classical.choose_spec (h_bridge_α α)).1
  have hCα_bound : ∀ α : M, ∀ {u : M → ℝ}, Measurable u →
      tsupport u ⊆ tsupport (ρ α : M → ℝ) →
      eLpNorm u p
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g ρ)
        ≤ ENNReal.ofReal (Cα α) *
            eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α u) p
              ((volume :
                Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                  (I := I) (M := M) α)) := fun α =>
    (Classical.choose_spec (h_bridge_α α)).2
  refine ⟨∑ α ∈ S, Cα α, Finset.sum_nonneg (fun α _ => (hCα_pos α).le), ?_⟩
  intro u hu_meas
  rw [DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_def
    (I := I) (M := M) g]
  have h_eLpNorm_eq :
      eLpNorm u p (DifferentialGeometry.Integral.Measure.riemannianMeasure
          (I := I) g ρ) =
        eLpNorm (∑ α ∈ S, fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) p
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g ρ) := by
    refine eLpNorm_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Finset.sum_apply]
    change u x = ∑ α ∈ S, (ρ α : M → ℝ) x * u x
    have hsum : ∑ α ∈ S, (ρ α : M → ℝ) x = 1 :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one
        (I := I) (M := M) x
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [h_eLpNorm_eq]
  have h_aesm : ∀ α ∈ S,
      AEStronglyMeasurable (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g ρ) := by
    intro α _
    have hcont : Continuous (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x) :=
      (ρ α).contMDiff.continuous
    exact (hcont.measurable.mul hu_meas).aestronglyMeasurable
  refine (eLpNorm_sum_le h_aesm hp_one).trans ?_
  have h_per_α : ∀ α ∈ S,
      eLpNorm (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) p
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g ρ) ≤
      ENNReal.ofReal (Cα α) *
        wkpNormChart (I := I) (M := M) g 1 p u := by
    intro α _
    have h_supp : tsupport (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
        tsupport (ρ α : M → ℝ) := by
      have h_eq : (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) =
          (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x • u x) := by funext x; rfl
      rw [h_eq]
      exact tsupport_smul_subset_left
        (f := fun x : M => ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)
    have h_meas : Measurable (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) :=
      (ρ α).contMDiff.continuous.measurable.mul hu_meas
    have h_bridge := hCα_bound α h_meas h_supp
    refine h_bridge.trans ?_
    have h_ae :=
      DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_ae
        (I := I) (M := M) ρ α u
    have h_eLpNorm_eq :
        eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw I α
              (fun x : M => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) p
            ((volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)) =
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
              (I := I) (M := M) ρ α u) p
            ((volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I) (M := M) α)) :=
      eLpNorm_congr_ae h_ae.symm
    rw [h_eLpNorm_eq]
    have h1 :=
      DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushed_p_le_wkpNorm_one
        (I := I) (M := M) g (p := p) u α
    gcongr
  refine (Finset.sum_le_sum h_per_α).trans ?_
  rw [← Finset.sum_mul]
  gcongr
  rw [show (∑ α ∈ S, ENNReal.ofReal (Cα α)) = ENNReal.ofReal (∑ α ∈ S, Cα α) from ?_]
  refine (ENNReal.ofReal_sum_of_nonneg (fun α _ => (hCα_pos α).le)).symm

theorem w1pNormIntrinsicLp_le_const_mul_wkpNormChart_smooth_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I 𝓘(ℝ, ℝ) ∞ u →
        eLpNorm u p
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) ≤
          ENNReal.ofReal C *
            wkpNormChart (I := I) (M := M) g 1 p u := by
  obtain ⟨C, hC_nn, hbound⟩ :=
    eLpNorm_riemannianVolumeMeasure_le_const_mul_wkpNormChart_uniform
      (I := I) (M := M) g hp_one hp_top
  refine ⟨C, hC_nn, ?_⟩
  intro u hu_smooth
  exact hbound hu_smooth.continuous.measurable

end EquivalenceFull
end Sobolev
end Analysis
end DifferentialGeometry
