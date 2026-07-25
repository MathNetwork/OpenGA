import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.Banach
import DifferentialGeometry.Analysis.Sobolev.Chart.BanachCompleteness.Completeness
import DifferentialGeometry.Analysis.Integration.Measure.MeasureBridge
import DifferentialGeometry.Analysis.Integration.Measure.Rellich
import DifferentialGeometry.Analysis.Sobolev.Chart.AtlasNorm.Atlas
import DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.UniformSpace.UniformEmbedding


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [IsManifold I ∞ M] in
lemma chartPushed_eq_chartPushedRaw_pou_mul_on_target
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    chartPushed (I := I) (M := M) ρ α u y =
      chartPushedRaw I α (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) y := by
  classical
  rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α
    (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) hy]
  unfold chartPushed
  rfl

omit [IsManifold I ∞ M] in
lemma chartPushedRaw_pou_mul_ae_eq_chartPushed_on_target
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    (fun y => chartPushedRaw I α
        (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) y)
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)]
      chartPushed (I := I) (M := M) ρ α u := by
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  refine Filter.Eventually.of_forall (fun y hy => ?_)
  exact (chartPushed_eq_chartPushedRaw_pou_mul_on_target
    (I := I) (M := M) ρ α u hy).symm

omit [IsManifold I ∞ M] in

omit [FiniteDimensional ℝ E] in
lemma support_pou_mul_fun_subset
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    Function.support (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      Function.support ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := by
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h
  apply hx
  rw [h]; ring

omit [IsManifold I ∞ M] in

omit [FiniteDimensional ℝ E] in
lemma tsupport_pou_mul_fun_subset
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ) :
    tsupport (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆
      tsupport ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
  closure_mono (support_pou_mul_fun_subset (I := I) (M := M) ρ α u)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
lemma tsupport_pou_mul_fun_subset_chartAt_source
    (ρ : SmoothPartitionOfUnity M I M Set.univ)
    (hρ : ρ.IsSubordinate (fun α : M => (chartAt H α).source))
    (α : M) (u : M → ℝ) :
    tsupport (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x) ⊆ (chartAt H α).source :=
  (tsupport_pou_mul_fun_subset (I := I) (M := M) ρ α u).trans (hρ α)

omit [IsManifold I ∞ M] in

omit [FiniteDimensional ℝ E] in
lemma pou_continuous (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) :
    Continuous ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) := (ρ α).contMDiff.continuous

omit [IsManifold I ∞ M] in

omit [FiniteDimensional ℝ E] in
lemma pou_measurable (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) :
    Measurable ((ρ α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
  (pou_continuous (I := I) (M := M) ρ α).measurable

omit [IsManifold I ∞ M] in
lemma eLpNorm_chartPushed_eq_eLpNorm_chartPushedRaw_pou_mul
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    (p : ℝ≥0∞) :
    eLpNorm (chartPushed (I := I) (M := M) ρ α u) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) =
      eLpNorm (chartPushedRaw I α
            (fun x => (ρ α : C^∞⟮I, M; ℝ⟯) x * u x)) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) :=
  eLpNorm_congr_ae
    (chartPushedRaw_pou_mul_ae_eq_chartPushed_on_target
      (I := I) (M := M) ρ α u).symm

lemma fun_eq_finset_sum_pou_mul
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (u : M → ℝ) :
    u = fun x =>
      ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) x * u x := by
  classical
  funext x
  have hsum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  have h_eq : ∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) x * u x =
      (∑ α ∈ DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M),
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α : M → ℝ) x) * u x := by
    rw [Finset.sum_mul]
  rw [h_eq, hsum, one_mul]

omit [IsManifold I ∞ M] in
lemma eLpNorm_chartPushed_le_wkpNorm_chartPushed
    {k : ℕ} {p : ℝ≥0∞} (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M)
    (u : M → ℝ) :
    eLpNorm (chartPushed (I := I) (M := M) ρ α u) p
        ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
          (chartTargetEuclid (I := I) (M := M) α)) ≤
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M) ρ α u)
        (chartTargetEuclid (I := I) (M := M) α) :=
  Euclidean.wkpNorm_zero_le_wkpNorm

lemma exists_sup_chartDensity_on_pou_tsupport_image
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M)
    (h_supp_ne : (tsupport
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ)).Nonempty) :
    ∃ M_sup : ℝ, 0 < M_sup ∧
      ∀ y ∈ (extChartAt I α) '' (tsupport
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ)),
        DifferentialGeometry.Integral.Measure.chartDensity g α
          ((extChartAt I α).symm y) ≤ M_sup := by
  classical
  have hsub :
      tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  have hK_decomp :=
    image_extChartAt_tsupport_compact_subset_target
      (I := I) (M := M)
      (u := ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)) (α := α) hsub
  obtain ⟨hK_compact, hK_sub_target⟩ := hK_decomp
  have hK_ne : ((extChartAt I α) '' (tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ))).Nonempty := h_supp_ne.image _
  exact exists_sup_chartDensity_on_compact_pos (I := I) (M := M)
    g α hK_compact hK_ne hK_sub_target

lemma eLpNorm_pou_mul_riemannianMeasure_le_const_mul_eLpNorm_chartPushed_per_u
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M)
    {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    {u : M → ℝ} (hu_meas : Measurable u) :
    ∃ C : ℝ, 0 < C ∧
      eLpNorm
          (fun x => (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
              : C^∞⟮I, M; ℝ⟯) x * u x) p
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M))
        ≤ ENNReal.ofReal C *
            eLpNorm
              (chartPushed (I := I) (M := M)
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) p
              ((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
                (chartTargetEuclid (I := I) (M := M) α)) := by
  classical
  set ρα : M → ℝ := ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
    : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hρα_def
  set ρu : M → ℝ := fun x => ρα x * u x with hρu_def
  have hρα_meas : Measurable ρα :=
    pou_measurable (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
  have hρu_meas : Measurable ρu := hρα_meas.mul hu_meas
  have hρu_supp : tsupport ρu ⊆ (chartAt H α).source :=
    tsupport_pou_mul_fun_subset_chartAt_source (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M) α u
  obtain ⟨C, hC_pos, hbnd⟩ :=
    eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw
      (I := I) (M := M) g α hp_one hp_top hρu_meas hρu_supp
  refine ⟨C, hC_pos, ?_⟩
  refine hbnd.trans ?_
  have h_eq :=
    eLpNorm_chartPushed_eq_eLpNorm_chartPushedRaw_pou_mul (I := I) (M := M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u p
  rw [hρu_def, ← h_eq]

private noncomputable def chartLocalIntegralPouTsupport
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) : ℝ≥0∞ :=
  ∫⁻ x, (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ)).indicator (fun _ : M => (1 : ℝ≥0∞)) x
      ∂(DifferentialGeometry.Integral.Measure.chartLocalMeasure (I := I) g α)

private noncomputable def euclideanDensityIntegralPouTsupport
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) : ℝ≥0∞ :=
  ∫⁻ y in chartTargetEuclid (I := I) (M := M) α,
    ENNReal.ofReal
        (DifferentialGeometry.Integral.Measure.chartDensity g α
          ((extChartAt I α).symm
            ((toEuclidean (E := E)).symm y))) *
      (tsupport ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ)).indicator (fun _ : M => (1 : ℝ≥0∞))
        ((extChartAt I α).symm
          ((toEuclidean (E := E)).symm y))
      ∂(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))

private noncomputable def chartHaarFactor
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M) : ℝ≥0∞ :=
  chartLocalIntegralPouTsupport (I := I) (M := M) g α /
    euclideanDensityIntegralPouTsupport (I := I) (M := M) g α

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
