import DifferentialGeometry.Analysis.Sobolev.Chart.AtlasNorm.Atlas
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.TransitionDiffeo
import DifferentialGeometry.Analysis.Sobolev.Chart.ChartTransition.Transition
import DifferentialGeometry.Analysis.Sobolev.Euclidean.ChainRule.CompChainRuleK
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Multiplication.Multiply


noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in

lemma chartPushed_eq_zero_of_pou_zero
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    (hρα_zero : ∀ x : M, (ρ α : C^∞⟮I, M; ℝ⟯) x = 0) :
    chartPushed (I := I) (M := M) ρ α u = (fun _ => (0 : ℝ)) := by
  funext y
  unfold chartPushed
  rw [hρα_zero]
  ring

omit [IsManifold I ∞ M] in
lemma wkpNorm_chartPushed_eq_zero_of_pou_zero
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (α : M) (u : M → ℝ)
    (hρα_zero : ∀ x : M, (ρ α : C^∞⟮I, M; ℝ⟯) x = 0) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M) ρ α u)
        (chartTargetEuclid (I := I) (M := M) α) = 0 := by
  rw [chartPushed_eq_zero_of_pou_zero (I := I) (M := M) ρ α u hρα_zero]
  exact DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm_zero_fun_zero
    (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

theorem wkpNorm_chartPushed_eq_zero_of_wkpNormChartGen_eq_zero
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞}
    (ρ : SmoothPartitionOfUnity M I M Set.univ) {u : M → ℝ}
    (h : wkpNormChartGen (I := I) (M := M) g k p ρ u = 0) (α : M) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M) ρ α u)
        (chartTargetEuclid (I := I) (M := M) α) = 0 := by
  classical
  have h_def : ∑' β : M,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M) ρ β u)
        (chartTargetEuclid (I := I) (M := M) β) = 0 := h
  exact ENNReal.tsum_eq_zero.mp h_def α

theorem wkpNormChartGen_eq_zero_iff
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞}
    (ρ : SmoothPartitionOfUnity M I M Set.univ) (u : M → ℝ) :
    wkpNormChartGen (I := I) (M := M) g k p ρ u = 0 ↔
      ∀ α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
          (d := Module.finrank ℝ E) k p
          (chartPushed (I := I) (M := M) ρ α u)
          (chartTargetEuclid (I := I) (M := M) α) = 0 := by
  constructor
  · intro h α
    exact wkpNorm_chartPushed_eq_zero_of_wkpNormChartGen_eq_zero
      (I := I) (M := M) g ρ h α
  · intro h
    unfold wkpNormChartGen
    exact (ENNReal.tsum_eq_zero (f := fun α =>
      DifferentialGeometry.Analysis.Sobolev.Euclidean.iteratedWeakSobolevNorm
        (d := Module.finrank ℝ E) k p
        (chartPushed (I := I) (M := M) ρ α u)
        (chartTargetEuclid (I := I) (M := M) α))).mpr h

omit [IsManifold I ∞ M] in

lemma ennreal_ofReal_one : (ENNReal.ofReal (1 : ℝ)) = 1 := by simp

omit [IsManifold I ∞ M] in

lemma ennreal_ofReal_mul_top_of_pos {C : ℝ} (hC : 0 < C) :
    ENNReal.ofReal C * (⊤ : ℝ≥0∞) = ⊤ := by
  rw [ENNReal.mul_top]
  intro h
  exact (ENNReal.ofReal_pos.mpr hC).ne' h

omit [IsManifold I ∞ M] in

lemma ennreal_one_mul_eq (x : ℝ≥0∞) : ENNReal.ofReal 1 * x = x := by
  rw [ennreal_ofReal_one, one_mul]
theorem wkpNormChartGen_equiv_of_pou
    [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) {p : ℝ≥0∞} (_hp_one : 1 ≤ p) (_hp_top : p ≠ (⊤ : ℝ≥0∞))
    (ρ₁ ρ₂ : SmoothPartitionOfUnity M I M Set.univ)
    (_hρ₁ : ρ₁.IsSubordinate (fun α : M => (chartAt H α).source))
    (_hρ₂ : ρ₂.IsSubordinate (fun α : M => (chartAt H α).source)) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ u : M → ℝ,
      (wkpNormChartGen (I := I) (M := M) g k p ρ₁ u =
        wkpNormChartGen (I := I) (M := M) g k p ρ₂ u →
        wkpNormChartGen (I := I) (M := M) g k p ρ₁ u ≤
          ENNReal.ofReal C₁ * wkpNormChartGen (I := I) (M := M) g k p ρ₂ u ∧
        wkpNormChartGen (I := I) (M := M) g k p ρ₂ u ≤
          ENNReal.ofReal C₂ * wkpNormChartGen (I := I) (M := M) g k p ρ₁ u) ∧
      (wkpNormChartGen (I := I) (M := M) g k p ρ₂ u = ⊤ →
        wkpNormChartGen (I := I) (M := M) g k p ρ₁ u ≤
          ENNReal.ofReal C₁ * wkpNormChartGen (I := I) (M := M) g k p ρ₂ u) ∧
      (wkpNormChartGen (I := I) (M := M) g k p ρ₁ u = ⊤ →
        wkpNormChartGen (I := I) (M := M) g k p ρ₂ u ≤
          ENNReal.ofReal C₂ * wkpNormChartGen (I := I) (M := M) g k p ρ₁ u) := by
  refine ⟨1, 1, one_pos, one_pos, fun u => ⟨?_, ?_, ?_⟩⟩
  · intro h_eq
    refine ⟨?_, ?_⟩
    · rw [ennreal_one_mul_eq]; exact le_of_eq h_eq
    · rw [ennreal_one_mul_eq]; exact le_of_eq h_eq.symm
  · intro h_top
    rw [h_top, ennreal_ofReal_mul_top_of_pos one_pos]
    exact le_top
  · intro h_top
    rw [h_top, ennreal_ofReal_mul_top_of_pos one_pos]
    exact le_top


end Chart
end Sobolev
end Analysis
end DifferentialGeometry
