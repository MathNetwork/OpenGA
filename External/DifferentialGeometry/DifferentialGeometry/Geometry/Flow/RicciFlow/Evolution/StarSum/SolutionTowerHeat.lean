import DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.Evolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.SolutionResidual
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.TowerProducer










noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Tensor0SBundle DifferentialGeometry.Integral.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M]

private theorem localFrame_reindex
    {Idx Idx' : Type*} {n : WithTop ℕ∞} {u : Set M}
    (e : Idx' ≃ Idx)
    (frame : Idx -> (x : M) -> TangentSpace I x)
    (hframe : IsLocalFrameOn I E n frame u) :
    IsLocalFrameOn I E n (fun i x => frame (e i) x) u where
  linearIndependent := by
    intro x hx
    exact (hframe.linearIndependent hx).comp e e.injective
  generating := by
    intro x hx
    rw [show Set.range (fun i : Idx' => frame (e i) x) =
        Set.range (fun i : Idx => frame i x) by
      ext v
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, by simp⟩]
    exact hframe.generating hx
  contMDiffOn i := hframe.contMDiffOn (e i)

variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable [I.Boundaryless]
variable [IsManifold I ∞ M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [BoundarylessManifold I M]



def towerSolConst (k : Nat) : Real :=
  2 * Real.sqrt (Fintype.card (Fin (4 + k) -> Fin 3) : Real) *
    (((4 + k : Nat) : Real) * (3 : Real) ^ 2 + resStarCost k)




theorem towerHeatSol
    {alpha t0 omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (hS : IsSolutionOn (I := I) S)
    (hAlphaT0 : alpha < t0) (hT0Omega : t0 < omega)
    (hdim : Module.finrank Real E = 3) (k : Nat) :
    let D' := RealTimeInterval.closedOpen t0 omega hT0Omega
    let S' := S.timeRestrict D'
    TowerHeatBoundOn (D := D')
      (nablaKRm04NormSqIntrinsic (I := I) S')
      (nablaKNormLap (I := I) S') (towerSolConst k) k := by
  classical
  let D' := RealTimeInterval.closedOpen t0 omega hT0Omega
  let S' := S.timeRestrict D'
  change TowerHeatBoundOn (D := D')
    (nablaKRm04NormSqIntrinsic (I := I) S')
    (nablaKNormLap (I := I) S') (towerSolConst k) k
  have hS' : IsSolutionOn (I := I) S' := by
    simpa [S', D'] using isSoln_tailRestrict (I := I) hS hAlphaT0 hT0Omega
  intro t x
  let g := S'.base.metric (t : Real)
  let e : Fin 3 ≃ Fin (Module.finrank Real E) := finCongr hdim.symm
  let rawFrame := smoothOrthoFrame (I := I) g x
  let frame : Fin 3 -> (y : M) -> TangentSpace I y := fun i y => rawFrame (e i) y
  let u := smoothOrthoOpen (I := I) (M := M) x
  have hu : IsOpen u := by
    simpa [u] using smoothOrthoOpen_open (I := I) (M := M) x
  have hx : x ∈ u := by
    simpa [u] using mem_smoothOrthoOpen (I := I) (M := M) x
  have hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u := by
    simpa [frame, rawFrame, u] using
      localFrame_reindex (I := I) (M := M) e
        (smoothOrthoFrame (I := I) g x)
        (smoothOrtho_local (I := I) g x)
  have horthU : ∀ y : M, y ∈ u -> ∀ i j : Fin 3,
      g.inner y (frame i y) (frame j y) = if i = j then (1 : Real) else 0 := by
    intro y hy i j
    have h := smoothOrthoFrame_orthonormal (I := I) g x
      (interior_subset hy) (e i) (e j)
    simpa [frame, rawFrame] using h
  let basis := hframe.toBasisAt hx
  have horth : ∀ i j : Fin 3,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0 := by
    intro i j
    simpa [basis, IsLocalFrameOn.toBasisAt_coe] using horthU x hx i j
  have hdimT : ∀ y : M, Module.finrank Real (TangentSpace I y) = 3 := by
    intro y
    calc
      Module.finrank Real (TangentSpace I y) = Module.finrank Real E := rfl
      _ = 3 := hdim
  obtain ⟨T, _hTmem, hrest⟩ :=
    resStarSol (I := I) (S := S) hS hAlphaT0 hT0Omega k t
      frame hframe hu hdimT horthU
  obtain ⟨C, hCeq, hC, htail⟩ := hrest
  obtain ⟨hcompDt, hres⟩ := htail
  subst C
  let gInvAll := localFrameInv (I := I) S' frame hframe
  let gInvDtAll := localFrameInvDt (I := I) S' frame hframe
  have hreg0 :=
    tailFrameTimeReg (I := I) (S := S) hS hAlphaT0 hT0Omega frame hframe
  have hreg : MetricFrameTimeRegularityInFrameOnLocal
      (I := I) S' gInvAll gInvDtAll frame u := by
    simpa [S', D', gInvAll, gInvDtAll] using hreg0
  let gInv : Real -> Fin 3 -> Fin 3 -> Real := fun r => gInvAll r x
  have hinv : ∀ r : Real,
      MetricInverseInBasis_gen (I := I) (S'.base.metric r) x basis (gInv r) := by
    intro r i j
    constructor
    · simpa [gInv, gInvAll, basis, metricCompInFrame,
        IsLocalFrameOn.toBasisAt_coe] using
          (hreg.nondegenerateGram r x hx i j).1
    · simpa [gInv, gInvAll, basis, metricCompInFrame,
        IsLocalFrameOn.toBasisAt_coe] using
          (hreg.nondegenerateGram r x hx i j).2
  have hinvId : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin 3)) :=
    metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth
  have hgInv : gInv (t : Real) = identityInvMetric (Idx := Fin 3) :=
    invBasis_unique (I := I) g x basis _ _ (by simpa [g] using hinv (t : Real)) hinvId
  let ric : Fin 3 -> Fin 3 -> Real := fun i j =>
    S'.ricciAt (t : Real) x (vec2 (I := I) (basis i) (basis j))
  have hInvEvol :=
    inverseMetricEvolution_of_metricFrameTimeRegularity
      (I := I) S' hS' gInvAll gInvDtAll frame hreg
  have hgInvDt : ∀ i j : Fin 3,
      HasDerivWithinAt (fun r : Real => gInv r i j)
        (2 * (∑ p : Fin 3, ∑ q : Fin 3,
          gInv (t : Real) i p * gInv (t : Real) j q * ric p q))
        D'.carrier (t : Real) := by
    intro i j
    simpa [gInv, gInvAll, ric, basis, inverseMetricEvolutionRHSInFrame,
      raisedRicciCompInFrame_apply, ricciCompInFrame,
      IsLocalFrameOn.toBasisAt_coe] using hInvEvol t x hx i j
  let Tdot : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (4 + k) x :=
    metricTrace0S2TensorInBasis (I := I) basis (identityInvMetric (Idx := Fin 3))
        (nablaKRm04Field (I := I) S' (t : Real) (k + 2) x) + T x
  have hT : ∀ I0 : Fin (4 + k) -> Fin 3,
      HasDerivWithinAt
        (fun r : Real => tensor0SComponent (I := I)
          (nablaKRm04Field (I := I) S' r k x) (fun i => basis i) I0)
        (tensor0SComponent (I := I) Tdot (fun i => basis i) I0)
        D'.carrier (t : Real) := by
    intro I0
    simpa [S', D', Tdot, basis, IsLocalFrameOn.toBasisAt_coe] using
      hcompDt x hx I0
  have hst (j : Nat) : stNormSq (I := I) S' (t : Real) j x basis =
      nablaKRm04NormSqIntrinsic (I := I) S' j (t : Real) x := by
    simpa [stNormSq, nablaKRm04NormSqIntrinsic] using
      (compNormSqMulti_orthoBasis_eq_normSq0S (I := I)
        (S'.base.metric (t : Real)) basis (by simpa [g] using horth)
        (nablaKRm04Field (I := I) S' (t : Real) j x))
  have hresid : ∀ m : Fin (4 + k) -> Fin 3,
      |tensor0SComponent (I := I)
          (Tdot - metricTrace0S2TensorInBasis (I := I) basis (gInv (t : Real))
            (nablaKRm04Field (I := I) S' (t : Real) (k + 2) x))
          (fun i => basis i) m| ≤
        resStarCost k * ∑ j ∈ Finset.range (k + 1),
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S' j (t : Real) x) *
          Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S' (k - j) (t : Real) x) := by
    intro m
    have hcancel :
        Tdot - metricTrace0S2TensorInBasis (I := I) basis (gInv (t : Real))
            (nablaKRm04Field (I := I) S' (t : Real) (k + 2) x) = T x := by
      rw [hgInv]
      dsimp only [Tdot]
      abel
    rw [hcancel]
    simpa [S', D', basis, IsLocalFrameOn.toBasisAt_coe, hst] using
      hres x hx m
  have hlevel : compNormSqMulti (fun I0 : Fin (4 + k) -> Fin 3 =>
      tensor0SComponent (I := I) (nablaKRm04Field (I := I) S' (t : Real) k x)
        (fun i => basis i) I0) ≤
      nablaKRm04NormSqIntrinsic (I := I) S' k (t : Real) x := by
    exact le_of_eq (by
      simpa [tensor0SComponent_apply, nablaKRm04NormSqIntrinsic] using
        (compNormSqMulti_orthoBasis_eq_normSq0S (I := I)
          (S'.base.metric (t : Real)) basis (by simpa [g] using horth)
          (nablaKRm04Field (I := I) S' (t : Real) k x)))
  have hRic : ∀ p q : Fin 3, |ric p q| ≤
      (Fintype.card (Fin 3) : Real) *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S' 0 (t : Real) x) := by
    intro p q
    simpa [ric, SolutionOn.ricciAt, SolutionFamily.ricciAt,
      nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
      SolutionFamily.rm04, metricRm04] using
        (metricRicciComp_le (I := I) (g := S'.base.metric (t : Real))
          basis (by simpa [g] using horth) p q)
  have hheat := nablaKNormHeatAt (I := I) S' k t x basis gInv ric Tdot
    (fun r => by simpa [MetricInverseInBasis, MetricInverseInBasis_gen] using hinv r)
    hT hgInvDt
  have hreact0 := nablaKReactionAt_le (I := I) S' (t : Real) x basis
    (gInv (t : Real)) ric Tdot
    (nablaKRm04NormSqIntrinsic (I := I) S')
    (by simpa [g] using horth) hgInv hlevel hRic
    (resStarCost k) hC hresid
  have hreact : |nablaKReactionAt (I := I) S' k (t : Real) x basis
      (gInv (t : Real)) ric Tdot| ≤
      towerReactionSum (M := M) (nablaKRm04NormSqIntrinsic (I := I) S')
        (towerSolConst k) k (t : Real) x := by
    simpa [towerSolConst] using hreact0
  refine ⟨nablaKNormLap (I := I) S' k (t : Real) x +
      (-2 * nablaKRm04NormSqIntrinsic (I := I) S' (k + 1) (t : Real) x +
        nablaKReactionAt (I := I) S' k (t : Real) x basis
          (gInv (t : Real)) ric Tdot), hheat, ?_⟩
  linarith [le_abs_self (nablaKReactionAt (I := I) S' k (t : Real) x basis
    (gInv (t : Real)) ric Tdot), hreact]

end DifferentialGeometry.PDE.RicciFlow
