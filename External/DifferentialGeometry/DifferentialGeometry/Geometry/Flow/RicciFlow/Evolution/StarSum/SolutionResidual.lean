import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.TowerHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.TowerSwapRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.UhlenbeckBaseProducer








namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]




omit [NeZero (Module.finrank ℝ E)] in
theorem resStarSol [CompactSpace M]
    {alpha t0 omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (hS : IsSolutionOn (I := I) S)
    (hAlphaT0 : alpha < t0) (hT0Omega : t0 < omega)
    (k : Nat)
    (t : RealTimeInterval.RegularTime
      (RealTimeInterval.closedOpen t0 omega hT0Omega))
    {u : Set M}
    (frame : Fin 3 -> (y : M) -> TangentSpace I y)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u)
    (hdim : ∀ y : M, Module.finrank Real (TangentSpace I y) = 3)
    (horthU : ∀ y : M, y ∈ u -> ∀ i j : Fin 3,
      ((S.timeRestrict
        (RealTimeInterval.closedOpen t0 omega hT0Omega)).base.metric
          (t : Real)).inner y (frame i y) (frame j y) =
        if i = j then (1 : Real) else 0) :
    ∃ T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) (4 + k),
      StarSum2 (I := I)
          (S.timeRestrict (RealTimeInterval.closedOpen t0 omega hT0Omega))
          (t : Real) k T ∧
      ∃ C : Real, C = resStarCost k ∧ 0 ≤ C ∧
        (∀ (y : M) (hy : y ∈ u) (I0 : Fin (4 + k) -> Fin 3),
          HasDerivWithinAt
            (fun r : Real =>
              tensor0SComponent (I := I)
                (nablaKRm04Field (I := I)
                  (S.timeRestrict
                    (RealTimeInterval.closedOpen t0 omega hT0Omega))
                  r k y)
                (fun i => frame i y) I0)
            (tensor0SComponent (I := I)
              (metricTrace0S2TensorInBasis (I := I) (hframe.toBasisAt hy)
                  (identityInvMetric (Idx := Fin 3))
                  (nablaKRm04Field (I := I)
                    (S.timeRestrict
                      (RealTimeInterval.closedOpen t0 omega hT0Omega))
                    (t : Real) (k + 2) y) + T y)
              (fun i => frame i y) I0)
            (RealTimeInterval.closedOpen t0 omega hT0Omega).carrier (t : Real)) ∧
        (∀ (y : M) (hy : y ∈ u) (m : Fin (4 + k) -> Fin 3),
          |T y (fun p => frame (m p) y)| ≤
            C * ∑ j ∈ Finset.range (k + 1),
              Real.sqrt (stNormSq (I := I)
                (S.timeRestrict
                  (RealTimeInterval.closedOpen t0 omega hT0Omega))
                (t : Real) j y (hframe.toBasisAt hy)) *
              Real.sqrt (stNormSq (I := I)
                (S.timeRestrict
                  (RealTimeInterval.closedOpen t0 omega hT0Omega))
                (t : Real) (k - j) y (hframe.toBasisAt hy))) := by
  classical
  let D' := RealTimeInterval.closedOpen t0 omega hT0Omega
  let S' := S.timeRestrict D'
  have hS' : IsSolutionOn (I := I) S' := by
    simpa [S', D'] using isSoln_tailRestrict (I := I) hS hAlphaT0 hT0Omega
  obtain ⟨hframe1, baseDt, chrDt, hrm, hchr, hchrId, hswap⟩ :=
    tailTowerData (I := I) hS hAlphaT0 hT0Omega frame hframe hu
  have hbase := rm04Base_of_sol (I := I) S' hS' t hdim
  have hrm' : ∀ (y : M), y ∈ u -> ∀ m : Fin 4 -> Fin 3,
      HasDerivWithinAt (fun s : Real => lfBase (I := I) S' frame s y m)
        (baseDt (t : Real) y m) D'.carrier (t : Real) := by
    intro y hy m
    simpa only [lfBase, S', D'] using hrm t y hy m
  have hchr' : ∀ (y : M), y ∈ u -> ∀ i a p : Fin 3,
      HasDerivWithinAt
        (fun s : Real => lfChr (I := I) S' frame hframe1 s y i a p)
        (chrDt (t : Real) y i a p) D'.carrier (t : Real) := by
    intro y hy i a p
    simpa only [lfChr, S', D'] using hchr t y hy i a p
  have hchrId' : ∀ (y : M), y ∈ u -> ∀ i j p : Fin 3,
      chrDt (t : Real) y i j p =
        -ricciCovDerivCompInFrame (I := I) S' frame (t : Real) y i j p
        -ricciCovDerivCompInFrame (I := I) S' frame (t : Real) y j i p
        +ricciCovDerivCompInFrame (I := I) S' frame (t : Real) y p i j := by
    intro y hy i j p
    simpa only [S', D'] using hchrId t y hy (horthU y hy) i j p
  have hswap' : ∀ (y : M), y ∈ u -> ∀ (k' : Nat) (d : Fin 3)
      (m : Fin (4 + k') -> Fin 3),
      HasDerivWithinAt
        (fun s : Real =>
          extDerivFun (I := I)
            (fun z : M =>
              iteratedRmComp (I := I) frame (lfChr (I := I) S' frame hframe1)
                (lfBase (I := I) S' frame) k' s z m)
            y (frame d y))
        (extDerivFun (I := I)
          (fun z : M =>
            iteratedRmCompDt (I := I) frame (lfChr (I := I) S' frame hframe1)
              chrDt (lfBase (I := I) S' frame) baseDt k' (t : Real) z m)
          y (frame d y))
        D'.carrier (t : Real) := by
    intro y hy k' d m
    simpa only [lfChr, lfBase, S', D'] using
      hswap k' m (t : Real) t.2 y hy (frame d y)
  simpa only [S', D'] using
    resStarBoundLF (I := I) S' hS' k t frame hframe1 hu hdim horthU
      hbase baseDt chrDt hrm' hchr' hchrId' hswap'

end DifferentialGeometry.PDE.RicciFlow
