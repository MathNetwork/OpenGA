import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.TailChristoffel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.FrameTowerRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedRmTowerHeatEq










namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]




omit [NeZero (Module.finrank ℝ E)] in
theorem frameTowerSwap [CompactSpace M]
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (hS : IsSolutionOn (I := I) S)
    {Idx : Type} [Fintype Idx]
    (frame : Idx -> (y : M) -> TangentSpace I y) {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hframe1 : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    (hu : IsOpen u)
    (baseDt : Real -> M -> (Fin 4 -> Idx) -> Real)
    (chrDt : Real -> M -> Idx -> Idx -> Idx -> Real)
    (hrm : ∀ (t : RealTimeInterval.RegularTime
        (RealTimeInterval.closedOpen alpha omega hAlphaOmega))
        (x : M), x ∈ u -> ∀ m : Fin 4 -> Idx,
      HasDerivWithinAt
        (fun s : Real => frameComp0S (I := I) (S.base.rm04 s) frame x m)
        (baseDt (t : Real) x m)
        (RealTimeInterval.closedOpen alpha omega hAlphaOmega).carrier (t : Real))
    (hchr : ∀ (t : RealTimeInterval.RegularTime
        (RealTimeInterval.closedOpen alpha omega hAlphaOmega))
        (x : M), x ∈ u -> ∀ i a p : Idx,
      HasDerivWithinAt
        (fun s : Real => christoffelSymbolInFrame
          (S.family.connection s) frame hframe1 x i a p)
        (chrDt (t : Real) x i a p)
        (RealTimeInterval.closedOpen alpha omega hAlphaOmega).carrier (t : Real)) :
    ∀ (k : Nat) (m : Fin (4 + k) -> Idx),
      FixedBaseExtDerivTimeDerivativeOnRegular (I := I)
        (RealTimeInterval.closedOpen alpha omega hAlphaOmega).carrier
        (RealTimeInterval.closedOpen alpha omega hAlphaOmega).regular u
        (fun s x =>
          iteratedRmComp (I := I) frame
            (fun r y => christoffelSymbolInFrame
              (S.family.connection r) frame hframe1 y)
            (fun r => frameComp0S (I := I) (S.base.rm04 r) frame)
            k s x m)
        (fun t x =>
          iteratedRmCompDt (I := I) frame
            (fun r y => christoffelSymbolInFrame
              (S.family.connection r) frame hframe1 y)
            chrDt (fun r => frameComp0S (I := I) (S.base.rm04 r) frame)
            baseDt k t x m) := by
  classical
  let D := RealTimeInterval.closedOpen alpha omega hAlphaOmega
  let chr : Real -> M -> Idx -> Idx -> Idx -> Real := fun r y =>
    christoffelSymbolInFrame (S.family.connection r) frame hframe1 y
  let base : Real -> M -> (Fin 4 -> Idx) -> Real := fun r =>
    frameComp0S (I := I) (S.base.rm04 r) frame
  change ∀ (k : Nat) (m : Fin (4 + k) -> Idx),
    FixedBaseExtDerivTimeDerivativeOnRegular (I := I) D.carrier D.regular u
      (fun s x => iteratedRmComp (I := I) frame chr base k s x m)
      (fun t x => iteratedRmCompDt (I := I) frame chr chrDt base baseDt k t x m)
  have hsmooth : ∀ (k : Nat) (m : Fin (4 + k) -> Idx)
      (t : Real), t ∈ D.regular -> ∀ x : M, x ∈ u ->
      ContMDiffAt ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) 2
        (fun q : Real × M =>
          iteratedRmComp (I := I) frame chr base k q.1 q.2 m) (t, x) := by
    intro k m t ht x hx
    have hinf := frameTowerSmooth (I := I) hS frame hframe hframe1 hu
      x ⟨t, ht⟩ x (self_mem_chartLeviCivitaGoodSet (I := I) x) hx k m
    have h2inf : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by norm_cast
    simpa [chr, base, D] using hinf.of_le h2inf
  have hboth : ∀ k : Nat,
      (∀ (m : Fin (4 + k) -> Idx)
        (t : Real), t ∈ D.regular -> ∀ x : M, x ∈ u ->
          HasDerivWithinAt
            (fun s : Real => iteratedRmComp (I := I) frame chr base k s x m)
            (iteratedRmCompDt (I := I) frame chr chrDt base baseDt k t x m)
            D.carrier t) ∧
      (∀ m : Fin (4 + k) -> Idx,
        FixedBaseExtDerivTimeDerivativeOnRegular (I := I)
          D.carrier D.regular u
          (fun s x => iteratedRmComp (I := I) frame chr base k s x m)
          (fun t x =>
            iteratedRmCompDt (I := I) frame chr chrDt base baseDt k t x m)) := by
    intro k
    induction k with
    | zero =>
        have htime : ∀ (m : Fin 4 -> Idx)
            (t : Real), t ∈ D.regular -> ∀ x : M, x ∈ u ->
            HasDerivWithinAt
              (fun s : Real => iteratedRmComp (I := I) frame chr base 0 s x m)
              (iteratedRmCompDt (I := I) frame chr chrDt base baseDt 0 t x m)
              D.carrier t := by
          intro m t ht x hx
          simpa [iteratedRmComp_zero, iteratedRmCompDt_zero, base, D] using
            hrm ⟨t, ht⟩ x hx m
        refine ⟨htime, ?_⟩
        intro m
        exact fixedBaseOnRegSmooth (I := I) hu D.regular_isOpen
          (fun ht => D.regular_mem_nhds ht) (hsmooth 0 m) (htime m)
    | succ k ih =>
        have htime : ∀ (n : Fin (4 + (k + 1)) -> Idx)
            (t : Real), t ∈ D.regular -> ∀ x : M, x ∈ u ->
            HasDerivWithinAt
              (fun s : Real => iteratedRmComp (I := I) frame chr base (k + 1) s x n)
              (iteratedRmCompDt (I := I) frame chr chrDt base baseDt (k + 1) t x n)
              D.carrier t := by
          intro n t ht x hx
          have hstep := covDerivStepComp_hasDerivWithinAt
            (I := I) frame
            (iteratedRmComp (I := I) frame chr base k)
            (iteratedRmCompDt (I := I) frame chr chrDt base baseDt k)
            chr chrDt x n
            (fun m => ih.1 m t ht x hx)
            (fun i a p => by
              simpa [chr, D] using hchr ⟨t, ht⟩ x hx i a p)
            (fun m => ih.2 m t ht x hx (frame (n 0) x))
          simpa [iteratedRmComp_succ, iteratedRmCompDt_succ] using hstep
        refine ⟨htime, ?_⟩
        intro n
        exact fixedBaseOnRegSmooth (I := I) hu D.regular_isOpen
          (fun ht => D.regular_mem_nhds ht) (hsmooth (k + 1) n) (htime n)
  intro k m
  exact (hboth k).2 m




omit [NeZero (Module.finrank ℝ E)] in
theorem tailTowerData [CompactSpace M]
    {alpha t0 omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (hS : IsSolutionOn (I := I) S)
    (hAlphaT0 : alpha < t0) (hT0Omega : t0 < omega)
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    (frame : Idx -> (y : M) -> TangentSpace I y) {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) :
    ∃ hframe1 : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u,
      ∃ baseDt : Real -> M -> (Fin 4 -> Idx) -> Real,
        ∃ chrDt : Real -> M -> Idx -> Idx -> Idx -> Real,
          (∀ (t : RealTimeInterval.RegularTime
              (RealTimeInterval.closedOpen t0 omega hT0Omega))
              (x : M), x ∈ u -> ∀ m : Fin 4 -> Idx,
            HasDerivWithinAt
              (fun s : Real => frameComp0S (I := I)
                ((S.timeRestrict
                  (RealTimeInterval.closedOpen t0 omega hT0Omega)).base.rm04 s)
                frame x m)
              (baseDt (t : Real) x m)
              (RealTimeInterval.closedOpen t0 omega hT0Omega).carrier (t : Real)) ∧
          (∀ (t : RealTimeInterval.RegularTime
              (RealTimeInterval.closedOpen t0 omega hT0Omega))
              (x : M), x ∈ u -> ∀ i a p : Idx,
            HasDerivWithinAt
              (fun s : Real => christoffelSymbolInFrame
                ((S.timeRestrict
                  (RealTimeInterval.closedOpen t0 omega hT0Omega)).family.connection s)
                frame hframe1 x i a p)
              (chrDt (t : Real) x i a p)
              (RealTimeInterval.closedOpen t0 omega hT0Omega).carrier (t : Real)) ∧
          (∀ (t : RealTimeInterval.RegularTime
              (RealTimeInterval.closedOpen t0 omega hT0Omega))
              (x : M), x ∈ u ->
              (∀ i j : Idx,
                ((S.timeRestrict
                  (RealTimeInterval.closedOpen t0 omega hT0Omega)).base.metric
                    (t : Real)).inner x (frame i x) (frame j x) =
                  if i = j then (1 : Real) else 0) ->
              ∀ i j p : Idx,
                chrDt (t : Real) x i j p =
                  -ricciCovDerivCompInFrame (I := I)
                      (S.timeRestrict
                        (RealTimeInterval.closedOpen t0 omega hT0Omega))
                      frame (t : Real) x i j p
                  -ricciCovDerivCompInFrame (I := I)
                      (S.timeRestrict
                        (RealTimeInterval.closedOpen t0 omega hT0Omega))
                      frame (t : Real) x j i p
                  +ricciCovDerivCompInFrame (I := I)
                      (S.timeRestrict
                        (RealTimeInterval.closedOpen t0 omega hT0Omega))
                      frame (t : Real) x p i j) ∧
          ∀ (k : Nat) (m : Fin (4 + k) -> Idx),
            FixedBaseExtDerivTimeDerivativeOnRegular (I := I)
              (RealTimeInterval.closedOpen t0 omega hT0Omega).carrier
              (RealTimeInterval.closedOpen t0 omega hT0Omega).regular u
              (fun s x =>
                iteratedRmComp (I := I) frame
                  (fun r y => christoffelSymbolInFrame
                    ((S.timeRestrict
                      (RealTimeInterval.closedOpen t0 omega hT0Omega)).family.connection r)
                    frame hframe1 y)
                  (fun r => frameComp0S (I := I)
                    ((S.timeRestrict
                      (RealTimeInterval.closedOpen t0 omega hT0Omega)).base.rm04 r)
                    frame)
                  k s x m)
              (fun t x =>
                iteratedRmCompDt (I := I) frame
                  (fun r y => christoffelSymbolInFrame
                    ((S.timeRestrict
                      (RealTimeInterval.closedOpen t0 omega hT0Omega)).family.connection r)
                    frame hframe1 y)
                  chrDt
                  (fun r => frameComp0S (I := I)
                    ((S.timeRestrict
                      (RealTimeInterval.closedOpen t0 omega hT0Omega)).base.rm04 r)
                    frame)
                  baseDt k t x m) := by
  classical
  let D' := RealTimeInterval.closedOpen t0 omega hT0Omega
  let S' := S.timeRestrict D'
  have hS' : IsSolutionOn (I := I) S' := by
    simpa [S', D'] using isSoln_tailRestrict (I := I) hS hAlphaT0 hT0Omega
  obtain ⟨hframe1, hgamma⟩ :=
    tailChristoffel (I := I) (Idx := Idx) hS hAlphaT0 hT0Omega frame hframe hu
  let baseDt : Real -> M -> (Fin 4 -> Idx) -> Real := fun r x m =>
    deriv (fun s : Real => frameComp0S (I := I) (S'.base.rm04 s) frame x m) r
  let gInv := localFrameInv (E := E) (I := I) S' frame hframe
  let nablaRic := fun (r : Real) (x : M) (d a b : Idx) =>
    ricciCovDerivCompInFrame (I := I) S' frame r x d a b
  let chrDt : Real -> M -> Idx -> Idx -> Idx -> Real := fun r x i j p =>
    christoffelEvolutionRHSInFrame (M := M) gInv nablaRic r x i j p
  have hrm : ∀ (t : RealTimeInterval.RegularTime D')
      (x : M), x ∈ u -> ∀ m : Fin 4 -> Idx,
        HasDerivWithinAt
          (fun s : Real => frameComp0S (I := I) (S'.base.rm04 s) frame x m)
          (baseDt (t : Real) x m) D'.carrier (t : Real) := by
    intro t x hx m
    have hinf := frameTowerSmooth (I := I) hS' frame hframe hframe1 hu
      x t x (self_mem_chartLeviCivitaGoodSet (I := I) x) hx 0 m
    have hline : ContMDiffAt (modelWithCornersSelf Real Real)
        ((modelWithCornersSelf Real Real).prod I) ∞
        (fun s : Real => (s, x)) (t : Real) :=
      contMDiffAt_id.prodMk contMDiffAt_const
    have hslice := hinf.comp (t : Real) hline
    have hdiff : DifferentiableAt Real
        (fun s : Real => frameComp0S (I := I) (S'.base.rm04 s) frame x m)
        (t : Real) := by
      have hcd : ContDiffAt Real ∞
          (fun s : Real => frameComp0S (I := I) (S'.base.rm04 s) frame x m)
          (t : Real) := by
        rw [← contMDiffAt_iff_contDiffAt]
        simpa only [iteratedRmComp_zero] using hslice
      exact hcd.differentiableAt (by simp)
    simpa only [baseDt] using hdiff.hasDerivAt.hasDerivWithinAt
  have hchr : ∀ (t : RealTimeInterval.RegularTime D')
      (x : M), x ∈ u -> ∀ i a p : Idx,
        HasDerivWithinAt
          (fun s : Real => christoffelSymbolInFrame
            (S'.family.connection s) frame hframe1 x i a p)
          (chrDt (t : Real) x i a p) D'.carrier (t : Real) := by
    intro t x hx i a p
    simpa only [chrDt, gInv, nablaRic, S', D'] using hgamma t x hx i a p
  have hswap := frameTowerSwap (I := I) hS' frame hframe hframe1 hu
    baseDt chrDt hrm hchr
  refine ⟨hframe1, baseDt, chrDt, ?_, ?_, ?_, ?_⟩
  · simpa only [S', D'] using hrm
  · simpa only [S', D'] using hchr
  · intro t x hx horth i j p
    have hinvId : ∀ e l : Idx, gInv (t : Real) x e l =
        if e = l then (1 : Real) else 0 := by
      intro e l
      have hleft := (localFrameInv_real (I := I) S' frame hframe
        (t : Real) x hx e l).1
      have horth' : ∀ a b : Idx,
          metricCompInFrame (I := I) S' frame (t : Real) x a b =
            if a = b then (1 : Real) else 0 := by
        intro a b
        simpa only [metricCompInFrame, SolutionOn.family_metric, S', D'] using
          horth a b
      simpa only [horth', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] using hleft
    simpa only [chrDt, nablaRic, S', D'] using
      christoffelRHS_id (M := M) gInv nablaRic hinvId i j p
  · simpa only [S', D'] using hswap

end DifferentialGeometry.PDE.RicciFlow
