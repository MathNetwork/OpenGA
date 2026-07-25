import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.NullSubmodule
import Mathlib.Analysis.Normed.Group.Uniform

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def wkpNormChartReal
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) : ℝ :=
  (wkpNormChart (I := I) (M := M) g k p u).toReal

@[simp]
lemma wkpNormChartReal_def
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    wkpNormChartReal (I := I) (M := M) g k p u =
      (wkpNormChart (I := I) (M := M) g k p u).toReal := rfl

lemma wkpNormChartReal_nonneg
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    0 ≤ wkpNormChartReal (I := I) (M := M) g k p u :=
  ENNReal.toReal_nonneg

lemma wkpNormChartReal_zero
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) :
    wkpNormChartReal (I := I) (M := M) g k p (fun _ : M => (0 : ℝ)) = 0 := by
  unfold wkpNormChartReal
  rw [wkpNormChart_zero_fun (I := I) (M := M) g hp]
  simp

lemma wkpNormChartReal_add_le
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (I := I) (M := M) g k p u)
    (hv : MemWkpChart (I := I) (M := M) g k p v) :
    wkpNormChartReal (I := I) (M := M) g k p (fun x => u x + v x) ≤
      wkpNormChartReal (I := I) (M := M) g k p u +
        wkpNormChartReal (I := I) (M := M) g k p v := by
  unfold wkpNormChartReal
  have hu_lt : wkpNormChart (I := I) (M := M) g k p u < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp hu
  have hv_lt : wkpNormChart (I := I) (M := M) g k p v < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp hv
  have hu_ne : wkpNormChart (I := I) (M := M) g k p u ≠ ⊤ := hu_lt.ne
  have hv_ne : wkpNormChart (I := I) (M := M) g k p v ≠ ⊤ := hv_lt.ne
  have hSum_le := wkpNormChart_add_le (I := I) (M := M) g hp hu hv
  have hRHS_ne : wkpNormChart (I := I) (M := M) g k p u +
      wkpNormChart (I := I) (M := M) g k p v ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hu_ne, hv_ne⟩
  have hToReal := ENNReal.toReal_mono hRHS_ne hSum_le
  rw [ENNReal.toReal_add hu_ne hv_ne] at hToReal
  exact hToReal

lemma wkpNormChartReal_const_smul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ} (hu : MemWkpChart (I := I) (M := M) g k p u) :
    wkpNormChartReal (I := I) (M := M) g k p (fun x => c * u x) =
      ‖c‖ * wkpNormChartReal (I := I) (M := M) g k p u := by
  unfold wkpNormChartReal
  rw [wkpNormChart_const_smul (I := I) (M := M) g hp c hu]
  rw [ENNReal.toReal_mul, toReal_enorm]

def wkpChartFun
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u : WkpChart (I := I) (M := M) g k p hp) : M → ℝ :=
  Subtype.val (α := (M → ℝ))
    (p := fun u => u ∈ wkpChartSubmodule (I := I) (M := M) g k p hp) u

lemma wkpChartFun_memWkpChart
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u : WkpChart (I := I) (M := M) g k p hp) :
    MemWkpChart (I := I) (M := M) g k p (wkpChartFun u) :=
  Subtype.property
    (α := (M → ℝ))
    (p := fun u => u ∈ wkpChartSubmodule (I := I) (M := M) g k p hp) u

@[simp]
lemma wkpChartFun_add
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u v : WkpChart (I := I) (M := M) g k p hp) :
    wkpChartFun (u + v) = fun x => wkpChartFun u x + wkpChartFun v x := by
  ext x
  rfl

@[simp]
lemma wkpChartFun_smul
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (c : ℝ) (u : WkpChart (I := I) (M := M) g k p hp) :
    wkpChartFun (c • u) = fun x => c * wkpChartFun u x := by
  ext x
  rfl

instance instNormWkpChart
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Norm (WkpChart (I := I) (M := M) g k p hp) where
  norm u := (wkpNormChart (I := I) (M := M) g k p (wkpChartFun u)).toReal

@[simp]
lemma norm_wkpChart_def
    [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u : WkpChart (I := I) (M := M) g k p hp) :
    ‖u‖ = (wkpNormChart (I := I) (M := M) g k p (wkpChartFun u)).toReal := rfl

lemma wkpChart_seminormedSpace_core
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    SeminormedSpace.Core ℝ (WkpChart (I := I) (M := M) g k p hp) where
  norm_nonneg u := ENNReal.toReal_nonneg
  norm_smul c u := by
    have hu_mem := wkpChartFun_memWkpChart u
    change (wkpNormChart (I := I) (M := M) g k p (wkpChartFun (c • u))).toReal =
      ‖c‖ * (wkpNormChart (I := I) (M := M) g k p (wkpChartFun u)).toReal
    rw [wkpChartFun_smul]
    rw [wkpNormChart_const_smul (I := I) (M := M) g hp c hu_mem]
    rw [ENNReal.toReal_mul, toReal_enorm]
  norm_triangle u v := by
    have hu_mem := wkpChartFun_memWkpChart u
    have hv_mem := wkpChartFun_memWkpChart v
    change (wkpNormChart (I := I) (M := M) g k p (wkpChartFun (u + v))).toReal ≤
      (wkpNormChart (I := I) (M := M) g k p (wkpChartFun u)).toReal +
        (wkpNormChart (I := I) (M := M) g k p (wkpChartFun v)).toReal
    rw [wkpChartFun_add]
    have h_add_le := wkpNormChart_add_le (I := I) (M := M) g hp hu_mem hv_mem
    have hu_lt : wkpNormChart (I := I) (M := M) g k p (wkpChartFun u) < ⊤ :=
      wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp hu_mem
    have hv_lt : wkpNormChart (I := I) (M := M) g k p (wkpChartFun v) < ⊤ :=
      wkpNormChart_lt_top_of_memWkpChart (I := I) (M := M) g hp hv_mem
    have hu_ne : wkpNormChart (I := I) (M := M) g k p (wkpChartFun u) ≠ ⊤ := hu_lt.ne
    have hv_ne : wkpNormChart (I := I) (M := M) g k p (wkpChartFun v) ≠ ⊤ := hv_lt.ne
    have hRHS_ne : wkpNormChart (I := I) (M := M) g k p (wkpChartFun u) +
        wkpNormChart (I := I) (M := M) g k p (wkpChartFun v) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hu_ne, hv_ne⟩
    have hToReal := ENNReal.toReal_mono hRHS_ne h_add_le
    rw [ENNReal.toReal_add hu_ne hv_ne] at hToReal
    exact hToReal

instance instSeminormedAddCommGroupWkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    SeminormedAddCommGroup (WkpChart (I := I) (M := M) g k p hp) :=
  SeminormedAddCommGroup.ofCore (wkpChart_seminormedSpace_core (I := I) (M := M) g k p hp)

instance instNormedSpaceRealWkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    NormedSpace ℝ (WkpChart (I := I) (M := M) g k p hp) where
  norm_smul_le c u := by
    have hu_mem := wkpChartFun_memWkpChart u
    change (wkpNormChart (I := I) (M := M) g k p (wkpChartFun (c • u))).toReal ≤
      ‖c‖ * (wkpNormChart (I := I) (M := M) g k p (wkpChartFun u)).toReal
    rw [wkpChartFun_smul]
    rw [wkpNormChart_const_smul (I := I) (M := M) g hp c hu_mem]
    rw [ENNReal.toReal_mul, toReal_enorm]

def WkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : Type _ :=
  SeparationQuotient (WkpChart (I := I) (M := M) g k p hp)

instance instAddCommGroupWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    AddCommGroup (WkpChartQuot (I := I) (M := M) g k p hp) :=
  inferInstanceAs (AddCommGroup (SeparationQuotient (WkpChart (I := I) (M := M) g k p hp)))

instance instNormedAddCommGroupWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    NormedAddCommGroup (WkpChartQuot (I := I) (M := M) g k p hp) :=
  inferInstanceAs (NormedAddCommGroup
    (SeparationQuotient (WkpChart (I := I) (M := M) g k p hp)))

instance instModuleWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Module ℝ (WkpChartQuot (I := I) (M := M) g k p hp) :=
  inferInstanceAs (Module ℝ (SeparationQuotient (WkpChart (I := I) (M := M) g k p hp)))

instance instNormedSpaceRealWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    NormedSpace ℝ (WkpChartQuot (I := I) (M := M) g k p hp) :=
  inferInstanceAs (NormedSpace ℝ (SeparationQuotient (WkpChart (I := I) (M := M) g k p hp)))

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
