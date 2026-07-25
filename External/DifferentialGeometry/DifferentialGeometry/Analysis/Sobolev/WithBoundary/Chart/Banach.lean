import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart.Defs
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.NullSubmodule
import Mathlib.Analysis.Normed.Group.Uniform

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

def wkpNormChartReal
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) : ℝ :=
  (wkpNormChart (n := n) (M := M) g k p u).toReal

@[simp]
lemma wkpNormChartReal_def
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    wkpNormChartReal (n := n) (M := M) g k p u =
      (wkpNormChart (n := n) (M := M) g k p u).toReal := rfl

lemma wkpNormChartReal_nonneg
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (u : M → ℝ) :
    0 ≤ wkpNormChartReal (n := n) (M := M) g k p u :=
  ENNReal.toReal_nonneg

lemma wkpNormChartReal_zero
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) :
    wkpNormChartReal (n := n) (M := M) g k p (fun _ : M => (0 : ℝ)) = 0 := by
  unfold wkpNormChartReal
  rw [wkpNormChart_zero_fun (n := n) (M := M) g hp]
  simp

lemma wkpNormChartReal_add_le
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : M → ℝ}
    (hu : MemWkpChart (n := n) (M := M) g k p u)
    (hv : MemWkpChart (n := n) (M := M) g k p v) :
    wkpNormChartReal (n := n) (M := M) g k p (fun x => u x + v x) ≤
      wkpNormChartReal (n := n) (M := M) g k p u +
        wkpNormChartReal (n := n) (M := M) g k p v := by
  unfold wkpNormChartReal
  have hu_lt : wkpNormChart (n := n) (M := M) g k p u < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp hu
  have hv_lt : wkpNormChart (n := n) (M := M) g k p v < ⊤ :=
    wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp hv
  have hu_ne : wkpNormChart (n := n) (M := M) g k p u ≠ ⊤ := hu_lt.ne
  have hv_ne : wkpNormChart (n := n) (M := M) g k p v ≠ ⊤ := hv_lt.ne
  have hSum_le := wkpNormChart_add_le (n := n) (M := M) g hp hu hv
  have hRHS_ne : wkpNormChart (n := n) (M := M) g k p u +
      wkpNormChart (n := n) (M := M) g k p v ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hu_ne, hv_ne⟩
  have hToReal := ENNReal.toReal_mono hRHS_ne hSum_le
  rw [ENNReal.toReal_add hu_ne hv_ne] at hToReal
  exact hToReal

lemma wkpNormChartReal_const_smul
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (c : ℝ) {u : M → ℝ} (hu : MemWkpChart (n := n) (M := M) g k p u) :
    wkpNormChartReal (n := n) (M := M) g k p (fun x => c * u x) =
      ‖c‖ * wkpNormChartReal (n := n) (M := M) g k p u := by
  unfold wkpNormChartReal
  rw [wkpNormChart_const_smul (n := n) (M := M) g hp c hu]
  rw [ENNReal.toReal_mul, toReal_enorm]

def wkpChartFun
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u : WkpChart (n := n) (M := M) g k p hp) : M → ℝ :=
  Subtype.val (α := (M → ℝ))
    (p := fun u => u ∈ wkpChartSubmodule (n := n) (M := M) g k p hp) u

lemma wkpChartFun_memWkpChart
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u : WkpChart (n := n) (M := M) g k p hp) :
    MemWkpChart (n := n) (M := M) g k p (wkpChartFun u) :=
  Subtype.property
    (α := (M → ℝ))
    (p := fun u => u ∈ wkpChartSubmodule (n := n) (M := M) g k p hp) u

@[simp]
lemma wkpChartFun_add
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u v : WkpChart (n := n) (M := M) g k p hp) :
    wkpChartFun (u + v) = fun x => wkpChartFun u x + wkpChartFun v x := by
  ext x
  rfl

@[simp]
lemma wkpChartFun_smul
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (c : ℝ) (u : WkpChart (n := n) (M := M) g k p hp) :
    wkpChartFun (c • u) = fun x => c * wkpChartFun u x := by
  ext x
  rfl

instance instNormWkpChart
    [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Norm (WkpChart (n := n) (M := M) g k p hp) where
  norm u := (wkpNormChart (n := n) (M := M) g k p (wkpChartFun u)).toReal

@[simp]
lemma norm_wkpChart_def
    [T2Space M] [SigmaCompactSpace M]
    {g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M}
    {k : ℕ} {p : ℝ≥0∞} {hp : 1 ≤ p}
    (u : WkpChart (n := n) (M := M) g k p hp) :
    ‖u‖ = (wkpNormChart (n := n) (M := M) g k p (wkpChartFun u)).toReal := rfl

lemma wkpChart_seminormedSpace_core
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    SeminormedSpace.Core ℝ (WkpChart (n := n) (M := M) g k p hp) where
  norm_nonneg u := ENNReal.toReal_nonneg
  norm_smul c u := by
    have hu_mem := wkpChartFun_memWkpChart u
    change (wkpNormChart (n := n) (M := M) g k p (wkpChartFun (c • u))).toReal =
      ‖c‖ * (wkpNormChart (n := n) (M := M) g k p (wkpChartFun u)).toReal
    rw [wkpChartFun_smul]
    rw [wkpNormChart_const_smul (n := n) (M := M) g hp c hu_mem]
    rw [ENNReal.toReal_mul, toReal_enorm]
  norm_triangle u v := by
    have hu_mem := wkpChartFun_memWkpChart u
    have hv_mem := wkpChartFun_memWkpChart v
    change (wkpNormChart (n := n) (M := M) g k p (wkpChartFun (u + v))).toReal ≤
      (wkpNormChart (n := n) (M := M) g k p (wkpChartFun u)).toReal +
        (wkpNormChart (n := n) (M := M) g k p (wkpChartFun v)).toReal
    rw [wkpChartFun_add]
    have h_add_le := wkpNormChart_add_le (n := n) (M := M) g hp hu_mem hv_mem
    have hu_lt : wkpNormChart (n := n) (M := M) g k p (wkpChartFun u) < ⊤ :=
      wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp hu_mem
    have hv_lt : wkpNormChart (n := n) (M := M) g k p (wkpChartFun v) < ⊤ :=
      wkpNormChart_lt_top_of_memWkpChart (n := n) (M := M) g hp hv_mem
    have hu_ne : wkpNormChart (n := n) (M := M) g k p (wkpChartFun u) ≠ ⊤ := hu_lt.ne
    have hv_ne : wkpNormChart (n := n) (M := M) g k p (wkpChartFun v) ≠ ⊤ := hv_lt.ne
    have hRHS_ne : wkpNormChart (n := n) (M := M) g k p (wkpChartFun u) +
        wkpNormChart (n := n) (M := M) g k p (wkpChartFun v) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hu_ne, hv_ne⟩
    have hToReal := ENNReal.toReal_mono hRHS_ne h_add_le
    rw [ENNReal.toReal_add hu_ne hv_ne] at hToReal
    exact hToReal

instance instSeminormedAddCommGroupWkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    SeminormedAddCommGroup (WkpChart (n := n) (M := M) g k p hp) :=
  SeminormedAddCommGroup.ofCore (wkpChart_seminormedSpace_core (n := n) (M := M) g k p hp)

instance instNormedSpaceRealWkpChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    NormedSpace ℝ (WkpChart (n := n) (M := M) g k p hp) where
  norm_smul_le c u := by
    have hu_mem := wkpChartFun_memWkpChart u
    change (wkpNormChart (n := n) (M := M) g k p (wkpChartFun (c • u))).toReal ≤
      ‖c‖ * (wkpNormChart (n := n) (M := M) g k p (wkpChartFun u)).toReal
    rw [wkpChartFun_smul]
    rw [wkpNormChart_const_smul (n := n) (M := M) g hp c hu_mem]
    rw [ENNReal.toReal_mul, toReal_enorm]

def WkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) : Type _ :=
  SeparationQuotient (WkpChart (n := n) (M := M) g k p hp)

instance instAddCommGroupWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    AddCommGroup (WkpChartQuot (n := n) (M := M) g k p hp) :=
  inferInstanceAs (AddCommGroup
    (SeparationQuotient (WkpChart (n := n) (M := M) g k p hp)))

instance instNormedAddCommGroupWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    NormedAddCommGroup (WkpChartQuot (n := n) (M := M) g k p hp) :=
  inferInstanceAs (NormedAddCommGroup
    (SeparationQuotient (WkpChart (n := n) (M := M) g k p hp)))

instance instModuleWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    Module ℝ (WkpChartQuot (n := n) (M := M) g k p hp) :=
  inferInstanceAs (Module ℝ
    (SeparationQuotient (WkpChart (n := n) (M := M) g k p hp)))

instance instNormedSpaceRealWkpChartQuot
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    (k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    NormedSpace ℝ (WkpChartQuot (n := n) (M := M) g k p hp) :=
  inferInstanceAs (NormedSpace ℝ
    (SeparationQuotient (WkpChart (n := n) (M := M) g k p hp)))

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
