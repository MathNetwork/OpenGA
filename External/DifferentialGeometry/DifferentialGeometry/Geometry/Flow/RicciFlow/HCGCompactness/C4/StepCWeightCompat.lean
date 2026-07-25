import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepB1Producers
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCNormalBump
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepCWeights

set_option autoImplicit false











noncomputable section

universe u uE uH uι

namespace DifferentialGeometry
namespace HCGCompactness

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open scoped Manifold ContDiff

section AlgebraCompat

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace Real E']



omit [NormedAddCommGroup E'] [NormedSpace ℝ E'] in
theorem raw_eq_normWeights {ι : Type uι} [Fintype ι]
    (num : ι → E' → Real) (z : E') (i : ι) :
    rawWeights num z i = normWeights num i z := by
  rfl



omit [NormedAddCommGroup E'] [NormedSpace ℝ E'] in
theorem cutRaw_eq_bumpNum {ι : Type uι} [DecidableEq ι]
    (χ : E' → Real) (ψ : ι → E' → Real) (J : ι → E' → E')
    (i0 i : ι) (z : E') :
    cutRaw (fun x => 1 - χ (J i0 x)) (fun j x => ψ j (J j x)) i0 i z =
      bumpNum χ ψ J i0 i z := by
  by_cases hi : i = i0
  · subst i
    simp [cutRaw, bumpNum]
  · simp [cutRaw, bumpNum, hi]



omit [NormedAddCommGroup E'] [NormedSpace ℝ E'] in
theorem rawBump_eq_weight {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (χ : E' → Real) (ψ : ι → E' → Real) (J : ι → E' → E')
    (i0 i : ι) (z : E') :
    rawWeights
        (cutRaw (fun x => 1 - χ (J i0 x)) (fun j x => ψ j (J j x)) i0) z i =
      normWeights (bumpNum χ ψ J i0) i z := by
  rw [raw_eq_normWeights]
  have hnum :
      cutRaw (fun x => 1 - χ (J i0 x)) (fun j x => ψ j (J j x)) i0 =
        bumpNum χ ψ J i0 := by
    funext j x
    exact cutRaw_eq_bumpNum χ ψ J i0 j x
  rw [hnum]

end AlgebraCompat

section NormalRawBridge

variable {E0 : Type uE} [NormedAddCommGroup E0] [InnerProductSpace Real E0]
variable [FiniteDimensional Real E0] [NeZero (Module.finrank Real E0)] [CompleteSpace E0]
variable {H0 : Type uH} [TopologicalSpace H0]
variable {I0 : ModelWithCorners Real E0 H0} [I0.Boundaryless]
variable {M0 : Type u} [TopologicalSpace M0] [ChartedSpace H0 M0]
variable [IsManifold I0 ∞ M0] [T2Space M0] [T2Space (TangentBundle I0 M0)]



omit [T2Space M0] in
omit [NeZero (Module.finrank ℝ E0)] in
theorem normalRaw_eq_bump {ι : Type*} [DecidableEq ι]
    (g : SmoothRiemannianMetric I0 M0) (p : ι → M0)
    (cut : ContDiffBump (0 : E0)) (f : ι → ContDiffBump (0 : E0))
    (i0 β i : ι) {z : E0}
    (hsrc : ∀ j, (normalChartAt (I := I0) g (p β)).symm z ∈
      (normalChartAt (I := I0) g (p j)).source) :
    normalRaw g p cut f i0 i ((normalChartAt (I := I0) g (p β)).symm z) =
      bumpNum (fun v : E0 => 1 - cut v) (fun j v => f j v)
        (fun j v => normalChartAt (I := I0) g (p j)
          ((normalChartAt (I := I0) g (p β)).symm v)) i0 i z := by
  simpa only [bumpNum] using
    (normalRaw_readout (I := I0) (z := z) g p cut f i0 β i hsrc)



omit [T2Space M0] in
omit [NeZero (Module.finrank ℝ E0)] in
theorem normalWeight_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I0 M0) (p : ι → M0)
    (cut : ContDiffBump (0 : E0)) (f : ι → ContDiffBump (0 : E0))
    (i0 β i : ι) {z : E0}
    (hsrc : ∀ j, (normalChartAt (I := I0) g (p β)).symm z ∈
      (normalChartAt (I := I0) g (p j)).source) :
    rawWeights
        (fun j v => normalRaw g p cut f i0 j
          ((normalChartAt (I := I0) g (p β)).symm v)) z i =
      normWeights
        (bumpNum (fun v : E0 => 1 - cut v) (fun j v => f j v)
          (fun j v => normalChartAt (I := I0) g (p j)
            ((normalChartAt (I := I0) g (p β)).symm v)) i0) i z := by
  simp only [rawWeights, normWeights]
  rw [normalRaw_eq_bump g p cut f i0 β i hsrc]
  congr 1
  apply Finset.sum_congr rfl
  intro j _hj
  exact normalRaw_eq_bump g p cut f i0 β j hsrc

end NormalRawBridge

end HCGCompactness
end DifferentialGeometry
