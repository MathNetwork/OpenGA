import DifferentialGeometry.Analysis.Elliptic.Lichnerowicz
import DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.LpClass


noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianPairingChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def hessPairingChart
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (b : M) : ℝ :=
  (chartHessFrobeniusSq (I := I) g
        (fun x : M => φ x + v x) b -
      chartHessFrobeniusSq (I := I) g
        (fun x : M => φ x - v x) b) / 4

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma hessPairingChart_def
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (b : M) :
    hessPairingChart (I := I) g φ v b =
      (chartHessFrobeniusSq (I := I) g
            (fun x : M => φ x + v x) b -
          chartHessFrobeniusSq (I := I) g
            (fun x : M => φ x - v x) b) / 4 := rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma smoothAddOfTwoSmooth
    (φ v : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => φ x + v x) :=
  φ.contMDiff.add v.contMDiff

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma smoothSubOfTwoSmooth
    (φ v : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => φ x - v x) :=
  φ.contMDiff.sub v.contMDiff

omit [CompactSpace M] in
theorem hessPairingChart_continuous
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) :
    Continuous (hessPairingChart (I := I) g φ v) := by
  classical
  unfold hessPairingChart
  have h1 := chartHessFrobeniusSq_continuous (I := I) g
    (smoothAddOfTwoSmooth (I := I) φ v)
  have h2 := chartHessFrobeniusSq_continuous (I := I) g
    (smoothSubOfTwoSmooth (I := I) φ v)
  exact (h1.sub h2).div_const 4

theorem hessPairingChart_memLp_two
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) :
    MemLp (hessPairingChart (I := I) g φ v) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  haveI : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact (hessPairingChart_continuous (I := I) g φ v).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def smoothScalarToContMDiffMap
    {g : SmoothRiemannianMetric I M} (v : SmoothScalar g) : C^∞⟮I, M; ℝ⟯ :=
  ⟨v.toFun, v.smooth⟩

noncomputable def hessPairingSmoothLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (hessPairingChart_memLp_two (I := I) g φ
      (smoothScalarToContMDiffMap (I := I) (g := g) v)).toLp _

@[simp] lemma hessPairingSmoothLp_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    hessPairingSmoothLp (I := I) (M := M) g φ v =
      (hessPairingChart_memLp_two (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v)).toLp _ := rfl

lemma hessPairingSmoothLp_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    (hessPairingSmoothLp (I := I) (M := M) g φ v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v)) :=
  MemLp.coeFn_toLp _

end HessianPairingChart
end Laplacian
end Analysis
end DifferentialGeometry

end
