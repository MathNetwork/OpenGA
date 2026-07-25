import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.CoordinateTowerRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RmRealizationBridgeAllK









namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]



omit [NeZero (Module.finrank ℝ E)] in
theorem frameTowerSmooth [CompactSpace M]
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (hS : IsSolutionOn (I := I) S)
    {Idx : Type} [Fintype Idx]
    (frame : Idx -> (y : M) -> TangentSpace I y) {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hframe1 : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    (hu : IsOpen u)
    (x0 : M)
    (t : RealTimeInterval.RegularTime
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega))
    (x : M) (hx : x ∈ chartLeviCivitaGoodSet (I := I) x0)
    (hxu : x ∈ u)
    (k : Nat) (idx : Fin (4 + k) -> Idx) :
    ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M =>
        iteratedRmComp (I := I) frame
          (fun s y => christoffelSymbolInFrame (S.family.connection s) frame
            hframe1 y)
          (fun s => frameComp0S (I := I) (S.base.rm04 s) frame)
          k p.1 p.2 idx)
      ((t : Real), x) := by
  classical
  let e := coordinateTrivializationAt (I := I) x0
  let b := Module.finBasis Real E
  let coeff : Idx -> CoordinateIdx (𝕜 := Real) E -> M -> Real :=
    fun i j y => e.localFrame_coeff I b j y (frame i y)
  have hxcoord : x ∈ coordinateFrameSet (I := I) x0 :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hcoeff : ∀ i j,
      ContMDiffAt I (modelWithCornersSelf Real Real) ∞
        (fun y : M => coeff i j y) x := by
    intro i j
    exact contMDiffAt_localFrame_coeff
      (I := I) (V := TangentSpace I) (e := e) (b := b)
      (s := frame i) (k := (∞ : WithTop ℕ∞)) hxcoord
      (hframe.contMDiffAt hu hxu i) j
  have hcoeffProd : ∀ i j,
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun p : Real × M => coeff i j p.2) ((t : Real), x) := by
    intro i j
    exact (hcoeff i j).comp ((t : Real), x)
      (contMDiffAt_snd (I := modelWithCornersSelf Real Real) (J := I)
        (n := (∞ : WithTop ℕ∞)) (p := ((t : Real), x)))
  have hsum :
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun p : Real × M =>
          ∑ slots : Fin (4 + k) -> CoordinateIdx (𝕜 := Real) E,
            (∏ q : Fin (4 + k), coeff (idx q) (slots q) p.2) *
              iteratedRmComp (I := I) (coordinateFrameAt (I := I) x0)
                (realizedChr (I := I) S x0) (realizedRmBase (I := I) S x0)
                k p.1 p.2 slots)
        ((t : Real), x) := by
    refine ContMDiffAt.sum fun slots _ => ?_
    refine (ContMDiffAt.prod fun q _ => ?_).mul
      (coordTowerSmooth (I := I) hS x0 t x hx k slots)
    exact hcoeffProd (idx q) (slots q)
  refine hsum.congr_of_eventuallyEq ?_
  have hdomain :
      {p : Real × M | p.2 ∈ u ∩ coordinateFrameSet (I := I) x0} ∈
        nhds ((t : Real), x) := by
    exact ((hu.inter (coordinateFrameSet_open (I := I) x0)).preimage
      continuous_snd).mem_nhds ⟨hxu, hxcoord⟩
  filter_upwards [hdomain] with p hp
  let A := nablaKRm04Field (I := I) S p.1 k p.2
  calc
    iteratedRmComp (I := I) frame
          (fun s y => christoffelSymbolInFrame (S.family.connection s) frame hframe1 y)
          (fun s => frameComp0S (I := I) (S.base.rm04 s) frame)
          k p.1 p.2 idx =
        A (fun q => frame (idx q) p.2) := by
      simpa [A, frameTuple] using
        iterRmLF_eq_nabla (I := I) S p.1 frame hframe1 hu k hp.1 idx
    _ = A (fun q =>
          ∑ j : CoordinateIdx (𝕜 := Real) E,
            coeff (idx q) j p.2 • coordinateFrameAt (I := I) x0 j p.2) := by
      congr 1
      funext q
      exact e.eq_sum_localFrame_coeff_smul hp.2
    _ = ∑ slots : Fin (4 + k) -> CoordinateIdx (𝕜 := Real) E,
          A (fun q => coeff (idx q) (slots q) p.2 •
            coordinateFrameAt (I := I) x0 (slots q) p.2) := by
      exact A.map_sum fun q j =>
        coeff (idx q) j p.2 • coordinateFrameAt (I := I) x0 j p.2
    _ = ∑ slots : Fin (4 + k) -> CoordinateIdx (𝕜 := Real) E,
          (∏ q : Fin (4 + k), coeff (idx q) (slots q) p.2) *
            A (fun q => coordinateFrameAt (I := I) x0 (slots q) p.2) := by
      refine Finset.sum_congr rfl fun slots _ => ?_
      rw [A.map_smul_univ, smul_eq_mul]
    _ = ∑ slots : Fin (4 + k) -> CoordinateIdx (𝕜 := Real) E,
          (∏ q : Fin (4 + k), coeff (idx q) (slots q) p.2) *
            iteratedRmComp (I := I) (coordinateFrameAt (I := I) x0)
              (realizedChr (I := I) S x0) (realizedRmBase (I := I) S x0)
              k p.1 p.2 slots := by
      refine Finset.sum_congr rfl fun slots _ => ?_
      rw [iteratedRmComp_eq_nablaKRm04Field (I := I) S x0 p.1 k hp.2 slots]
      rfl

end DifferentialGeometry.PDE.RicciFlow
