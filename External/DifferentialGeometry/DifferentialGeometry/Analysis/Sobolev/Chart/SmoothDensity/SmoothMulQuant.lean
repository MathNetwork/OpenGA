import DifferentialGeometry.Analysis.Sobolev.Chart.SmoothDensity.SmoothMul
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.MultiplyQuantK

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem MemWkpChart_smooth_mul_per_chart_quant
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (k : ℕ) {p : ℝ≥0∞} (hp_one : 1 ≤ p) (hp_top : p ≠ (⊤ : ℝ≥0∞))
    (φ : C^∞⟮I, M; ℝ⟯) (α : M) :
    ∃ K : ℝ, 0 < K ∧ ∀ {u : M → ℝ},
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (fun x => (φ : M → ℝ) x * u x))
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal K *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  obtain ⟨b, hb_smooth, _, hb_one_on_tsupp, hb_supp⟩ :=
    exists_chart_cutoff_M (I := I) (M := M) α
  have hbφ_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => b x * (φ : M → ℝ) x) :=
    hb_smooth.mul φ.contMDiff
  have hbφ_supp : tsupport (fun x : M => b x * (φ : M → ℝ) x) ⊆ (chartAt H α).source := by
    have h_eq : (fun x : M => b x * (φ : M → ℝ) x) = (fun x : M => b x • (φ : M → ℝ) x) := by
      funext x; rfl
    rw [h_eq]
    refine (tsupport_smul_subset_left (f := b) (g := (φ : M → ℝ))).trans hb_supp
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    smoothExtensionScalar_iteratedFDeriv_bound
      (I := I) (M := M) α hbφ_smooth hbφ_supp k
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set Λ : EuclN → ℝ := smoothExtensionScalar (I := I) (M := M) α
    (fun x : M => b x * (φ : M → ℝ) x) with hΛ_def
  have hΛ_smooth : ContDiff ℝ ∞ Λ := by
    rw [hΛ_def]
    exact contDiff_smoothExtensionScalar (I := I) (M := M) α hbφ_smooth hbφ_supp
  have hΛ_smooth_top : ContDiff ℝ (⊤ : ℕ∞) Λ := hΛ_smooth
  have hΛ_bound :
      ∀ j ≤ k, ∀ y ∈ Ω, ‖iteratedFDeriv ℝ j Λ y‖ ≤ C := fun j hj y _ =>
    hC_bound j hj y
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_smul_smooth_bounded_le
      (d := Module.finrank ℝ E) k hp_one hp_top hΩ_open hΛ_smooth_top hC_nn hΛ_bound
  refine ⟨K, hK_pos, ?_⟩
  intro u hu
  have h_factorize :
      (fun y : EuclN => chartPushed (I := I) (M := M)
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
        (fun x => (φ : M → ℝ) x * u x) y)
        =ᵐ[volume.restrict Ω]
      (fun y : EuclN => Λ y *
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y) := by
    refine (MeasureTheory.ae_restrict_iff' (chartTargetEuclid_measurableSet
      (I := I) (M := M) α)).mpr ?_
    refine Filter.Eventually.of_forall (fun y hy => ?_)
    rw [hΛ_def]
    exact chartPushed_mul_eq_smoothExtension_mul_chartPushed
      (I := I) (M := M) (α := α) (b := b) (φ := (φ : M → ℝ)) (u := u)
      hb_one_on_tsupp hy
  have h_norm_eq :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (fun x => (φ : M → ℝ) x * u x)) Ω =
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (fun y : EuclN => Λ y *
            chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u y) Ω :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_congr_ae
      (d := Module.finrank ℝ E) hp_one hΩ_open h_factorize
  rw [h_norm_eq]
  exact hK_bound hu

theorem wkpNormChart_smooth_mul_le
    [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) {p : ℝ≥0∞}
    (hp_one : 1 ≤ p) (hp_top : p ≠ ⊤)
    (φ : C^∞⟮I, M; ℝ⟯) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : M → ℝ}, MemWkpChart (I := I) (M := M) g k p u →
      wkpNormChart (I := I) (M := M) g k p (fun x => (φ : M → ℝ) x * u x)
        ≤ ENNReal.ofReal C * wkpNormChart (I := I) (M := M) g k p u := by
  classical
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_finset (I := I) (M := M) with hS_def
  have h_per_α : ∀ α : M, ∃ K : ℝ, 0 < K ∧ ∀ {u : M → ℝ},
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (fun x => (φ : M → ℝ) x * u x))
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal K *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α) := fun α =>
    MemWkpChart_smooth_mul_per_chart_quant (I := I) (M := M) k hp_one hp_top φ α
  let Kα : M → ℝ := fun α => (h_per_α α).choose
  have hKα_pos : ∀ α : M, 0 < Kα α := fun α => (h_per_α α).choose_spec.1
  have hKα_bound : ∀ α : M, ∀ {u : M → ℝ},
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
        (chartTargetEuclid (I := I) (M := M) α) →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (fun x => (φ : M → ℝ) x * u x))
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal (Kα α) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α) := fun α =>
    (h_per_α α).choose_spec.2
  by_cases hS_empty : S = ∅
  · refine ⟨1, one_pos, ?_⟩
    intro u _hu
    have h_zero_α : ∀ α : M, α ∉ S → ∀ x : M,
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 := fun α hα x =>
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_weight_zero_of_notMem
        (I := I) (M := M) hα x
    have h_chartPushed_zero : ∀ α : M, (∀ x : M,
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) →
        ∀ (v : M → ℝ),
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α v =
          (fun _ => (0 : ℝ)) := by
      intros α hzero v
      funext y
      unfold chartPushed
      rw [hzero]
      ring
    have h_all_zero : ∀ α : M, ∀ x : M,
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 := by
      intros α x
      apply h_zero_α α
      rw [hS_empty]
      exact Finset.notMem_empty α
    have h_per_α_zero : ∀ α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
          (chartTargetEuclid (I := I) (M := M) α) = 0 := by
      intro α
      rw [h_chartPushed_zero α (h_all_zero α) u]
      exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
        (d := Module.finrank ℝ E) hp_one
        (chartTargetEuclid_isOpen (I := I) (M := M) α)
    have h_per_α_zero_φu : ∀ α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (fun x => (φ : M → ℝ) x * u x))
          (chartTargetEuclid (I := I) (M := M) α) = 0 := by
      intro α
      rw [h_chartPushed_zero α (h_all_zero α) (fun x => (φ : M → ℝ) x * u x)]
      exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
        (d := Module.finrank ℝ E) hp_one
        (chartTargetEuclid_isOpen (I := I) (M := M) α)
    have h_lhs_zero : wkpNormChart (I := I) (M := M) g k p
        (fun x => (φ : M → ℝ) x * u x) = 0 := by
      unfold wkpNormChart
      rw [tsum_congr h_per_α_zero_φu]
      exact tsum_zero
    have h_rhs_zero : wkpNormChart (I := I) (M := M) g k p u = 0 := by
      unfold wkpNormChart
      rw [tsum_congr h_per_α_zero]
      exact tsum_zero
    rw [h_lhs_zero, h_rhs_zero, mul_zero]
  have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
  set K_max : ℝ := S.sup' hS_nonempty Kα with hKmax_def
  have hK_max_pos : 0 < K_max := by
    rw [hKmax_def]
    obtain ⟨α₀, hα₀⟩ := hS_nonempty
    exact lt_of_lt_of_le (hKα_pos α₀) (Finset.le_sup' Kα hα₀)
  have hKα_le_max : ∀ α ∈ S, Kα α ≤ K_max := fun α hα => Finset.le_sup' Kα hα
  refine ⟨K_max, hK_max_pos, ?_⟩
  intro u hu
  unfold wkpNormChart
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum ?_
  intro α
  by_cases hαS : α ∈ S
  · calc DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
            (fun x => (φ : M → ℝ) x * u x))
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Kα α) *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α) :=
          hKα_bound α (hu α)
      _ ≤ ENNReal.ofReal K_max *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
            (d := Module.finrank ℝ E) k p
            (chartPushed (I := I) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u)
            (chartTargetEuclid (I := I) (M := M) α) := by
          refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
          exact ENNReal.ofReal_le_ofReal (hKα_le_max α hαS)
  · have h_zero_pou : ∀ x : M,
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
          : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 := fun x =>
      DifferentialGeometry.Integral.Measure.chartAtlasPOU_weight_zero_of_notMem
        (I := I) (M := M) hαS x
    have h_chartPushed_φu :
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α
          (fun x => (φ : M → ℝ) x * u x) = (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [h_zero_pou]
      ring
    have h_chartPushed_u :
        chartPushed (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u =
          (fun _ => (0 : ℝ)) := by
      funext y
      unfold chartPushed
      rw [h_zero_pou]
      ring
    rw [h_chartPushed_φu, h_chartPushed_u]
    have h_zero_norm : DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p (fun _ : EuclN => (0 : ℝ))
        (chartTargetEuclid (I := I) (M := M) α) = 0 :=
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
        (d := Module.finrank ℝ E) hp_one
        (chartTargetEuclid_isOpen (I := I) (M := M) α)
    rw [h_zero_norm, mul_zero]

end Chart
end Sobolev
end Analysis
end DifferentialGeometry

end
