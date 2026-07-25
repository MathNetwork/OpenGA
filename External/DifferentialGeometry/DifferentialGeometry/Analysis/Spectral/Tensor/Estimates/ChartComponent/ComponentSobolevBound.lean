import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Components.Defs
import DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.Equivalence
import DifferentialGeometry.Analysis.Sobolev.Chart.Defs


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def tensorChartComponentScalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    M → ℝ :=
  tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma tensorChartComponentScalar_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx =
      tensorChartComponentPou (I := I) (M := M) g r s S α Idx Jdx := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComponentScalar_contMDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContMDiff I (𝓘(ℝ, ℝ)) ∞
      (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) :=
  tensorChartComponentPou_contMDiff (I := I) (M := M) g r s S α Idx Jdx

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem tensorChartComponentScalar_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    HasCompactSupport
      (tensorChartComponentScalar (I := I) (M := M) g r s S α Idx Jdx) :=
  tensorChartComponentPou_hasCompactSupport (I := I) (M := M) g r s S α Idx Jdx

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComponentScalar_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S₁ S₂ : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentScalar (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx =
      (fun x => tensorChartComponentScalar (I := I) (M := M)
          g r s S₁ α Idx Jdx x +
        tensorChartComponentScalar (I := I) (M := M)
          g r s S₂ α Idx Jdx x) := by
  funext x
  unfold tensorChartComponentScalar tensorChartComponentPou
  have hraw_add :
      tensorChartComponentRaw (I := I) (M := M) g r s (S₁ + S₂) α Idx Jdx x =
        tensorChartComponentRaw (I := I) (M := M) g r s S₁ α Idx Jdx x +
          tensorChartComponentRaw (I := I) (M := M) g r s S₂ α Idx Jdx x := by
    unfold tensorChartComponentRaw
    rw [show tensorTrivProj (I := I) (M := M) g r s (S₁ + S₂) α x =
          tensorTrivProj (I := I) (M := M) g r s S₁ α x +
            tensorTrivProj (I := I) (M := M) g r s S₂ α x from by
      unfold tensorTrivProj
      rw [show (S₁ + S₂).toSection x = S₁.toSection x + S₂.toSection x from
        by rw [SmoothCcTensor.toSection_add]; rfl]
      exact map_add _ _ _]
    exact map_add _ _ _
  rw [hraw_add]; ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
theorem tensorChartComponentScalar_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (c : ℝ) (S : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComponentScalar (I := I) (M := M) g r s (c • S) α Idx Jdx =
      (fun x => c * tensorChartComponentScalar (I := I) (M := M)
        g r s S α Idx Jdx x) := by
  funext x
  unfold tensorChartComponentScalar tensorChartComponentPou
  have hraw_smul :
      tensorChartComponentRaw (I := I) (M := M) g r s (c • S) α Idx Jdx x =
        c * tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx x := by
    unfold tensorChartComponentRaw
    rw [show tensorTrivProj (I := I) (M := M) g r s (c • S) α x =
          c • tensorTrivProj (I := I) (M := M) g r s S α x from by
      unfold tensorTrivProj
      rw [show (c • S).toSection x = c • S.toSection x from
        by rw [SmoothCcTensor.toSection_smul]; rfl]
      exact map_smul _ _ _]
    rw [map_smul]
    rfl
  rw [hraw_smul]; ring

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponent_memWkpChart_one_two
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemWkpChart (I := I) (M := M) g 1 2
      (tensorChartComponentScalar (I := I) (M := M)
        g r s S.toCcTensor α Idx Jdx) := by
  have hsmooth :=
    tensorChartComponentScalar_contMDiff (I := I) (M := M)
      g r s S.toCcTensor α Idx Jdx
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  exact DifferentialGeometry.Analysis.Sobolev.Equivalence.MemWkpChart_of_contMDiff
    (I := I) (M := M) g hp hsmooth

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponentScalar_wkpNormChart_lt_top
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    wkpNormChart (I := I) (M := M) g 1 2
      (tensorChartComponentScalar (I := I) (M := M)
        g r s S.toCcTensor α Idx Jdx) < ⊤ := by
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  exact wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp
    (tensorChartComponent_memWkpChart_one_two
      (I := I) (M := M) g r s S α Idx Jdx)

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponent_wkpNormChart_le_per_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧
      wkpNormChart (I := I) (M := M) g 1 2
        (tensorChartComponentScalar (I := I) (M := M)
          g r s S.toCcTensor α Idx Jdx) ≤
        ENNReal.ofReal C * (‖S‖₊ + 1) := by
  classical
  have h_lhs_lt_top := tensorChartComponentScalar_wkpNormChart_lt_top
    (I := I) (M := M) g r s S α Idx Jdx
  have h_lhs_ne_top : wkpNormChart (I := I) (M := M) g 1 2
      (tensorChartComponentScalar (I := I) (M := M)
        g r s S.toCcTensor α Idx Jdx) ≠ ⊤ := h_lhs_lt_top.ne
  set a : ℝ := (wkpNormChart (I := I) (M := M) g 1 2
      (tensorChartComponentScalar (I := I) (M := M)
        g r s S.toCcTensor α Idx Jdx)).toReal with ha_def
  have ha_nn : 0 ≤ a := ENNReal.toReal_nonneg
  refine ⟨a + 1, by linarith, ?_⟩
  have h_lhs_eq : wkpNormChart (I := I) (M := M) g 1 2
      (tensorChartComponentScalar (I := I) (M := M)
        g r s S.toCcTensor α Idx Jdx) = ENNReal.ofReal a := by
    rw [ha_def]
    exact (ENNReal.ofReal_toReal h_lhs_ne_top).symm
  rw [h_lhs_eq]
  have h1 : ENNReal.ofReal a ≤ ENNReal.ofReal (a + 1) := by
    apply ENNReal.ofReal_le_ofReal; linarith
  have h2 : ENNReal.ofReal (a + 1) ≤ ENNReal.ofReal (a + 1) * (‖S‖₊ + 1) := by
    have h_one_le : (1 : ℝ≥0∞) ≤ ((‖S‖₊ : ℝ≥0∞) + 1) := by
      exact le_add_self
    calc ENNReal.ofReal (a + 1)
        = ENNReal.ofReal (a + 1) * 1 := by rw [mul_one]
      _ ≤ ENNReal.ofReal (a + 1) * (‖S‖₊ + 1) :=
          mul_le_mul_of_nonneg_left h_one_le (by exact zero_le _)
  exact h1.trans h2

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorChartComponent_wkpNormChart_le_per_section_forall
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∀ S : SmoothCcTensorH1 g r s,
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNormChart (I := I) (M := M) g 1 2
          (tensorChartComponentScalar (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx) ≤
          ENNReal.ofReal C * (‖S‖₊ + 1) := fun S =>
  tensorChartComponent_wkpNormChart_le_per_section
    (I := I) (M := M) g r s S α Idx Jdx

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
