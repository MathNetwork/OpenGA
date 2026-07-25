import DifferentialGeometry.Analysis.Sobolev.Intrinsic.H1Lp


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Function
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicH1Lp

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def H1Submodule [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) :
    Submodule ℝ (Lp ℝ 2 (riemannianVolumeMeasure I M g)) where
  carrier := { u | MemH1Lp (I := I) (M := M) g u }
  add_mem' hu hv := MemH1Lp.add (I := I) (M := M) g hu hv
  zero_mem' := MemH1Lp.zero (I := I) (M := M) g
  smul_mem' c _ hu := MemH1Lp.const_smul (I := I) (M := M) g c hu

@[simp]
lemma mem_H1Submodule_iff
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure I M g)) :
    u ∈ H1Submodule (I := I) (M := M) g ↔ MemH1Lp (I := I) (M := M) g u := Iff.rfl

end Laplacian
end Analysis
end DifferentialGeometry

end
