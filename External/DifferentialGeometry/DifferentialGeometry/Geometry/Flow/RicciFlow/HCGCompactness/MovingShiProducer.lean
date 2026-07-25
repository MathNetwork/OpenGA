import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BernsteinTruncate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.StarSum.SolutionTowerHeat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.TowerNormRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicciTowerTrace
import DifferentialGeometry.Geometry.Operator.GradientRegularity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.HCGCompactness
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M]
variable [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [BoundarylessManifold I M]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [IsManifold I 2 M]
  [CompactSpace M] [BoundarylessManifold I M] in


omit [SigmaCompactSpace M] in
theorem rm04_bound_can
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (Rm04 : Real -> Tensor04Section (I := I) (M := M))
    (hRm : ∀ t ∈ Set.Ico alpha omega,
      Rm04RealizesConnection (I := I) (S.base.metric t)
        (metricCov (I := I) (M := M) (S.base.metric t)) (Rm04 t))
    (hbound : exists K : Real, forall t : Real, forall x : M,
      alpha <= t -> t < omega ->
        normSq0S (I := I) (S.base.metric t) x 4 (Rm04 t x) <= K) :
    exists K : Real, forall t : Real, forall x : M,
      alpha <= t -> t < omega ->
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) <= K := by
  obtain ⟨K, hK⟩ := hbound
  refine ⟨K, fun t x htAlpha htOmega => ?_⟩
  have hcan :
      Rm04RealizesConnection (I := I) (S.base.metric t)
        (metricCov (I := I) (M := M) (S.base.metric t)) (S.base.rm04 t) := by
    simpa [SolutionFamily.rm04, metricCov] using
      (metricCurvData (I := I) (M := M) (S.base.metric t)).h_rm04
  have heq := rm04_eq_of_realizes (I := I) (S.base.metric t)
    (metricCov (I := I) (M := M) (S.base.metric t)) hcan
    (hRm t ⟨htAlpha, htOmega⟩) x
  rw [heq]
  exact hK t x htAlpha htOmega




theorem movingRmBoundSol
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (beta : Real) (hBeta : beta ∈ Set.Ioo alpha omega) (order : Nat)
    (hdim : Module.finrank Real E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hbound : exists K0 : Real, forall t : Real, forall x : M,
      alpha <= t -> t < omega ->
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) <= K0) :
    ∃ KRm : Real, 0 <= KRm ∧
      ∀ psi : Real, psi ∈ Set.Ico beta omega ->
        ∀ k : Nat, k <= order -> ∀ t : Real, t ∈ Set.Icc beta psi -> ∀ x : M,
          nablaKRm04NormSqIntrinsic (I := I) S k t x <= KRm := by
  classical
  obtain ⟨K0, hK0⟩ := hbound
  obtain ⟨t0, hAlphaT0, hT0Beta⟩ := exists_between hBeta.1
  have hT0Omega : t0 < omega := hT0Beta.trans hBeta.2
  have hShift : alpha - t0 < omega - t0 := sub_lt_sub_right hAlphaOmega t0
  let DShift := RealTimeInterval.closedOpen (alpha - t0) (omega - t0) hShift
  let SShift : SolutionOn (I := I) (M := M) DShift :=
    (S.timeShift t0).timeRestrict DShift
  have hSShift : IsSolutionOn (I := I) SShift := by
    apply isSoln_timeRestrict (I := I) (isSolutionOn_timeShift (I := I) hS t0)
    · intro s hs
      change s + t0 ∈ Set.Ico alpha omega
      change s ∈ Set.Ico (alpha - t0) (omega - t0) at hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · intro s hs
      change s + t0 ∈ Set.Ioo alpha omega
      change s ∈ Set.Ioo (alpha - t0) (omega - t0) at hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hZeroOmega : 0 < omega - t0 := sub_pos.mpr hT0Omega
  let D0 := RealTimeInterval.closedOpen 0 (omega - t0) hZeroOmega
  let S0 : SolutionOn (I := I) (M := M) D0 := SShift.timeRestrict D0
  have hS0 : IsSolutionOn (I := I) S0 := by
    simpa only [S0, D0, DShift] using
      (isSoln_tailRestrict (I := I) hSShift (sub_neg.mpr hAlphaT0) hZeroOmega)
  have hHeat (k : Nat) :
      TowerHeatBoundOn (D := D0)
        (nablaKRm04NormSqIntrinsic (I := I) S0)
        (nablaKNormLap (I := I) S0) (towerSolConst k) k := by
    simpa only [S0, D0, DShift] using
      (towerHeatSol (I := I) hSShift (sub_neg.mpr hAlphaT0) hZeroOmega hdim k)
  let delta : Real := beta - t0
  have hDelta : 0 < delta := by simpa only [delta] using sub_pos.mpr hT0Beta
  let K : Real := max 1 K0
  have hKOne : 1 <= K := by exact le_max_left 1 K0
  have hKPos : 0 < K := lt_of_lt_of_le zero_lt_one hKOne
  have hK0K : K0 <= K := by exact le_max_right 1 K0
  let aScale : Real := K * (omega - t0)
  have hScale : 0 <= aScale := by
    exact mul_nonneg hKPos.le hZeroOmega.le
  let levels : Finset Nat := Finset.range (order + 1)
  have hLevels : levels.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [levels, Finset.mem_range]
    omega
  let c : Real := max 0 (levels.sup' hLevels towerSolConst)
  have hc : 0 <= c := le_max_left _ _
  have hLevel (k : Nat) (hk : k <= order) : towerSolConst k <= c := by
    have hkMem : k ∈ levels := by
      simp only [levels, Finset.mem_range]
      omega
    exact (Finset.le_sup' towerSolConst hkMem).trans (le_max_right _ _)
  let B : Nat -> Real := fun k =>
    (towerConst c aScale k) ^ 2 * K ^ 2 / delta ^ k
  let KRm : Real := levels.sup' hLevels B
  have hKRm : 0 <= KRm := by
    have hB0 : 0 <= B 0 := by
      simp only [B, pow_zero, div_one]
      positivity
    have hZeroMem : 0 ∈ levels := by
      simp only [levels, Finset.mem_range]
      omega
    exact hB0.trans (Finset.le_sup' B hZeroMem)
  refine ⟨KRm, hKRm, ?_⟩
  intro psi hPsi k hk t ht x
  have hT : 0 < psi - t0 := by linarith [hT0Beta, hPsi.1]
  have hSlab : Set.Icc 0 (psi - t0) ⊆ D0.carrier := by
    intro s hs
    change s ∈ Set.Ico 0 (omega - t0)
    exact ⟨hs.1, by linarith [hs.2, hPsi.2]⟩
  have hRegular : forall s : Real, s ∈ Set.Icc 0 (psi - t0) -> 0 < s ->
      s ∈ D0.regular := by
    intro s hs hsPos
    change s ∈ Set.Ioo 0 (omega - t0)
    exact ⟨hsPos, by linarith [hs.2, hPsi.2]⟩
  have hw0 : forall s : Real, s ∈ Set.Icc 0 (psi - t0) -> forall y : M,
      nablaKRm04NormSqIntrinsic (I := I) S0 0 s y <= K ^ 2 := by
    intro s hs y
    have hRaw := hK0 (s + t0) y (by linarith [hAlphaT0, hs.1])
      (by linarith [hs.2, hPsi.2])
    have hRaw' : nablaKRm04NormSqIntrinsic (I := I) S0 0 s y <= K0 := by
      simpa [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, S0, SShift,
        SolutionOn.timeRestrict, SolutionOn.timeShift, SolutionFamily.timeShift] using hRaw
    nlinarith [hK0K, hKOne]
  have hTK : psi - t0 <= aScale / K := by
    calc
      psi - t0 <= omega - t0 := by linarith [hPsi.2]
      _ = aScale / K := by
        apply (eq_div_iff (ne_of_gt hKPos)).2
        dsimp only [aScale]
        ring
  have hLap : forall j : Nat, forall s : Real, s ∈ Set.Icc 0 (psi - t0) ->
      0 < s -> forall y : M,
        heatOperatorWithDrift (I := I) (flowG (I := I) S0) s
          (fun _z : M => (0 : TangentSpace I _z))
          (nablaKRm04NormSqIntrinsic (I := I) S0 j s) y =
            nablaKNormLap (I := I) S0 j s y := by
    intro j s _hs _hsPos y
    rw [heatOperatorWithDrift_zero_drift, heatOperator_eq_laplacianAt,
      laplacianAt_eq]
    rfl
  have hwCont : forall j : Nat, ContinuousOn
      (fun p : Real × M => nablaKRm04NormSqIntrinsic (I := I) S0 j p.1 p.2)
      (spacetimeSlab (M := M) (psi - t0)) := by
    intro j
    have hJoint := (towerNorm_joint (I := I) hSShift j).continuousOn
    have hSub : spacetimeSlab (M := M) (psi - t0) ⊆ DShift.regular ×ˢ Set.univ := by
      intro p hp
      change p.1 ∈ Set.Icc 0 (psi - t0) ∧ p.2 ∈ Set.univ at hp
      change p.1 ∈ Set.Ioo (alpha - t0) (omega - t0) ∧ p.2 ∈ Set.univ
      exact ⟨⟨by linarith [hAlphaT0, hp.1.1], by linarith [hp.1.2, hPsi.2]⟩, hp.2⟩
    have hfun :
        (fun p : Real × M => nablaKRm04NormSqIntrinsic (I := I) S0 j p.1 p.2) =
          (fun p : Real × M => nablaKRm04NormSqIntrinsic (I := I) SShift j p.1 p.2) := by
      funext p
      simp only [nablaKRm04NormSqIntrinsic]
      rw [nablaKRm_eq_iterCov (I := I) S0 p.1 j,
        nablaKRm_eq_iterCov (I := I) SShift p.1 j]
      rfl
    rw [hfun]
    exact hJoint.mono hSub
  have hwSpace : forall j : Nat, forall s : Real, s ∈ Set.Icc 0 (psi - t0) ->
      0 < s -> forall y : M,
        MDifferentiableAt I (modelWithCornersSelf Real Real)
          (nablaKRm04NormSqIntrinsic (I := I) S0 j s) y := by
    intro j s _hs _hsPos y
    exact (nablaKNorm_smooth (I := I) S0 s j).contMDiffAt.mdifferentiableAt (by simp)
  have htShiftMem : t - t0 ∈ Set.Icc 0 (psi - t0) :=
    ⟨by linarith [hT0Beta, ht.1], by linarith [ht.2]⟩
  have htShiftPos : 0 < t - t0 := by linarith [hT0Beta, ht.1]
  have hEstimate := BernsteinTower.estimate_of_heat (I := I)
    (D := D0) (flowG (I := I) S0)
    (w := nablaKRm04NormSqIntrinsic (I := I) S0)
    (wLap := nablaKNormLap (I := I) S0) towerSolConst
    K aScale (psi - t0) hT hKPos hScale hSlab hRegular
    (fun j s y => nablaKRm04NormSqIntrinsic_nonneg (I := I) S0 j s y)
    hw0 hTK hHeat hLap hwCont hwSpace
    (fun j s _hs _hsPos y => gradientFun_mdiffAt (I := I) (S0.base.metric s)
      (nablaKNorm_smooth (I := I) S0 s j) y)
    k c hc
    (fun j hj => hLevel j (hj.trans hk)) htShiftMem htShiftPos x
  have hNum : 0 <= (towerConst c aScale k) ^ 2 * K ^ 2 := by positivity
  have hPow : delta ^ k <= (t - t0) ^ k := by
    gcongr
    linarith [ht.1]
  have hUniform : nablaKRm04NormSqIntrinsic (I := I) S0 k (t - t0) x <=
      (towerConst c aScale k) ^ 2 * K ^ 2 / delta ^ k :=
    hEstimate.trans (div_le_div_of_nonneg_left hNum (pow_pos hDelta k) hPow)
  have hField :
      nablaKRm04Field (I := I) S0 (t - t0) k =
        nablaKRm04Field (I := I) S t k := by
    have hTime : t - t0 + t0 = t := by ring
    rw [nablaKRm_eq_iterCov (I := I) S0 (t - t0) k,
      nablaKRm_eq_iterCov (I := I) S t k]
    simp [S0, SShift, SolutionOn.timeRestrict, SolutionOn.timeShift,
      SolutionFamily.timeShift, SolutionFamily.rm04, hTime]
  have hUniformS : nablaKRm04NormSqIntrinsic (I := I) S k t x <= B k := by
    unfold nablaKRm04NormSqIntrinsic at hUniform ⊢
    rw [hField] at hUniform
    simpa [B, S0, SShift, SolutionOn.timeRestrict, SolutionOn.timeShift,
      SolutionFamily.timeShift] using hUniform
  have hkMem : k ∈ levels := by
    simp only [levels, Finset.mem_range]
    omega
  exact hUniformS.trans (Finset.le_sup' B hkMem)




theorem movingShiBoundN
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (beta : Real) (hBeta : beta ∈ Set.Ioo alpha omega) (order : Nat)
    (hdim : Module.finrank Real E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hbound : exists K0 : Real, forall t : Real, forall x : M,
      alpha <= t -> t < omega ->
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) <= K0) :
    exists KShi : Real, 0 <= KShi ∧
      forall psi : Real, psi ∈ Set.Ico beta omega ->
        MovingShiBoundOn (I := I) Set.univ beta psi
          (fun _ t => S.base.metric t) order KShi := by
  classical
  obtain ⟨KRm, hKRm, hRm⟩ :=
    movingRmBoundSol (I := I) beta hBeta order hdim hS hbound
  let levels : Finset Nat := Finset.range (order + 1)
  have hLevels : levels.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [levels, Finset.mem_range]
    omega
  let A : Nat -> Real := fun k =>
    (Module.finrank Real E : Real) ^ ((2 + k) + 2) * KRm
  let KShi : Real := Real.sqrt (levels.sup' hLevels A)
  have hKShi : 0 <= KShi := Real.sqrt_nonneg _
  refine ⟨KShi, hKShi, ?_⟩
  intro psi hPsi k hk _i t ht x _hx
  have hRmK := hRm psi hPsi k hk t ht x
  have hRic := ricTower_normSq_le (I := I) S t k x
  have hRicA :
      normSq0S (I := I) (S.base.metric t) x (2 + k)
          (ricCovTower (I := I) (S.base.metric t) (S.base.metric t) k x) <= A k := by
    calc
      _ <= (Module.finrank Real E : Real) ^ ((2 + k) + 2) *
          nablaKRm04NormSqIntrinsic (I := I) S k t x := hRic
      _ <= (Module.finrank Real E : Real) ^ ((2 + k) + 2) * KRm :=
        mul_le_mul_of_nonneg_left hRmK (by positivity)
      _ = A k := rfl
  have hkMem : k ∈ levels := by
    simp only [levels, Finset.mem_range]
    omega
  have hTerm : Real.sqrt (A k) <= KShi := by
    exact (Real.sqrt_le_sqrt (Finset.le_sup' A hkMem))
  exact (Real.sqrt_le_sqrt hRicA).trans hTerm



theorem movingShiBoundSol
    {alpha omega : Real} {hAlphaOmega : alpha < omega}
    {S : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen alpha omega hAlphaOmega)}
    (hdim : Module.finrank Real E = 3)
    (hS : IsSolutionOn (I := I) S)
    (hbound : exists K0 : Real, forall t : Real, forall x : M,
      alpha <= t -> t < omega ->
        normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) <= K0) :
    ∃ KShi : Real, 0 <= KShi ∧ ∃ tShi : Real, tShi ∈ Set.Ico alpha omega ∧
      ∀ psi : Real, psi ∈ Set.Ico tShi omega ->
        MovingShiBoundOn (I := I) Set.univ tShi psi
          (fun _ t => S.base.metric t) 3 KShi := by
  obtain ⟨tShi, hAlphaShi, hShiOmega⟩ := exists_between hAlphaOmega
  obtain ⟨KShi, hKShi, hShi⟩ :=
    movingShiBoundN (I := I) tShi ⟨hAlphaShi, hShiOmega⟩ 3 hdim hS hbound
  exact ⟨KShi, hKShi, tShi, ⟨hAlphaShi.le, hShiOmega⟩, hShi⟩

end DifferentialGeometry.PDE.RicciFlow
