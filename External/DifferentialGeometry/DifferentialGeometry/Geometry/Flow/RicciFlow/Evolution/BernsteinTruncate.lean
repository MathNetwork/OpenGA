import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.BernsteinShiSolution

set_option autoImplicit false










noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [I.Boundaryless] [CompactSpace M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

namespace BernsteinTower




theorem estimate_of_heat
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily
      (I := I) (M := M) Real)
    {w wLap : Nat -> Real -> M -> Real}
    (levelC : Nat -> Real)
    (K aScale T : Real)
    (hT : 0 < T) (hK : 0 < K) (haScale : 0 <= aScale)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular)
    (hw_nonneg : forall k : Nat, forall t : Real, forall x : M, 0 <= w k t x)
    (hw0_bound : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      w 0 t x <= K ^ 2)
    (hTK : T <= aScale / K)
    (hheat : forall k : Nat, TowerHeatBoundOn (D := D) w wLap (levelC k) k)
    (hLap : forall k : Nat, forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
        (fun _y : M => (0 : TangentSpace I _y)) (w k t) x = wLap k t x)
    (hw_cont : forall k : Nat, ContinuousOn (fun p : Real × M => w k p.1 p.2)
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T))
    (hw_space : forall k : Nat, forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall y : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (w k t) y)
    (hw_grad : forall k : Nat, forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (w k t) y) x)
    (m : Nat) (c : Real) (hc : 0 <= c)
    (hlevelC : forall k : Nat, k <= m -> levelC k <= c)
    {t : Real} (htmem : t ∈ Set.Icc 0 T) (htpos : 0 < t) (x : M) :
    w m t x <= (towerConst c aScale m) ^ 2 * K ^ 2 / t ^ m := by
  classical
  let w' : Nat -> Real -> M -> Real := fun k =>
    if k <= m then w k else fun _ _ => 0
  let wLap' : Nat -> Real -> M -> Real := fun k =>
    if k <= m then wLap k else fun _ _ => 0
  have hw'_le : forall k : Nat, k <= m -> w' k = w k := by
    intro k hk
    simp only [w', if_pos hk]
  have hw'_gt : forall k : Nat, ¬ k <= m -> w' k = fun _ _ => 0 := by
    intro k hk
    simp only [w', if_neg hk]
  have hwLap'_le : forall k : Nat, k <= m -> wLap' k = wLap k := by
    intro k hk
    simp only [wLap', if_pos hk]
  have hwLap'_gt : forall k : Nat, ¬ k <= m -> wLap' k = fun _ _ => 0 := by
    intro k hk
    simp only [wLap', if_neg hk]
  have hw'_val_le : forall k : Nat, k <= m -> forall s : Real, forall y : M,
      w' k s y = w k s y := by
    intro k hk s y
    rw [hw'_le k hk]
  have hw'_val_gt : forall k : Nat, ¬ k <= m -> forall s : Real, forall y : M,
      w' k s y = 0 := by
    intro k hk s y
    rw [hw'_gt k hk]
  have hwLap'_val_le : forall k : Nat, k <= m -> forall s : Real, forall y : M,
      wLap' k s y = wLap k s y := by
    intro k hk s y
    rw [hwLap'_le k hk]
  have hwLap'_val_gt : forall k : Nat, ¬ k <= m -> forall s : Real, forall y : M,
      wLap' k s y = 0 := by
    intro k hk s y
    rw [hwLap'_gt k hk]
  have hw'_nonneg : forall k : Nat, forall s : Real, forall y : M, 0 <= w' k s y := by
    intro k s y
    by_cases hk : k <= m
    · rw [hw'_val_le k hk]
      exact hw_nonneg k s y
    · rw [hw'_val_gt k hk]
  have hreact_eq : forall k : Nat, k <= m -> forall s : Real, forall y : M,
      towerReactionSum (M := M) w' c k s y = towerReactionSum (M := M) w c k s y := by
    intro k hk s y
    unfold towerReactionSum
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hjk : j <= k := by omega
    have hj_le : j <= m := le_trans hjk hk
    have hkj_le : k - j <= m := le_trans (Nat.sub_le k j) hk
    rw [hw'_val_le j hj_le, hw'_val_le (k - j) hkj_le, hw'_val_le k hk]
  let B : BernsteinTower (I := I) G :=
    { D := D
      w := w'
      wLap := wLap'
      c := c
      K := K
      α := aScale
      T := T
      hT := hT
      hc := hc
      hK := hK
      hα := haScale
      hslab := hslab
      hregular := hregular
      hw_nonneg := by
        intro k s _hs y
        exact hw'_nonneg k s y
      hw0_bound := by
        intro s hs y
        rw [hw'_val_le 0 (Nat.zero_le m)]
        exact hw0_bound s hs y
      hTK := hTK
      hheat := by
        intro k tau y
        rcases lt_trichotomy k m with hlt | heq | hgt
        · have hk_le : k <= m := le_of_lt hlt
          have hk1_le : k + 1 <= m := hlt
          obtain ⟨d, hderiv, hle⟩ := hheat k tau y
          refine ⟨d, ?_, ?_⟩
          · have hfun : (fun s : Real => w' k s y) = (fun s : Real => w k s y) := by
              funext s
              rw [hw'_val_le k hk_le]
            rw [hfun]
            exact hderiv
          · rw [hwLap'_val_le k hk_le, hw'_val_le (k + 1) hk1_le,
              hreact_eq k hk_le]
            have hmono : towerReactionSum (M := M) w (levelC k) k (tau : Real) y <=
                towerReactionSum (M := M) w c k (tau : Real) y :=
              towerReactionSum_mono_const w (hlevelC k hk_le) k (tau : Real) y
            linarith
        · subst heq
          have hk_le : k <= k := le_rfl
          have hk1_gt : ¬ k + 1 <= k := by omega
          obtain ⟨d, hderiv, hle⟩ := hheat k tau y
          refine ⟨d, ?_, ?_⟩
          · have hfun : (fun s : Real => w' k s y) = (fun s : Real => w k s y) := by
              funext s
              rw [hw'_val_le k hk_le]
            rw [hfun]
            exact hderiv
          · rw [hwLap'_val_le k hk_le, hw'_val_gt (k + 1) hk1_gt,
              hreact_eq k hk_le]
            have hmono : towerReactionSum (M := M) w (levelC k) k (tau : Real) y <=
                towerReactionSum (M := M) w c k (tau : Real) y :=
              towerReactionSum_mono_const w (hlevelC k hk_le) k (tau : Real) y
            have hnn : 0 <= w (k + 1) (tau : Real) y := hw_nonneg (k + 1) (tau : Real) y
            nlinarith
        · have hk_gt : ¬ k <= m := by omega
          have hk1_gt : ¬ k + 1 <= m := by omega
          refine ⟨0, ?_, ?_⟩
          · have hfun : (fun s : Real => w' k s y) = (fun _s : Real => (0 : Real)) := by
              funext s
              rw [hw'_val_gt k hk_gt]
            rw [hfun]
            exact hasDerivWithinAt_const _ _ _
          · rw [hwLap'_val_gt k hk_gt, hw'_val_gt (k + 1) hk1_gt]
            have hreact0 : towerReactionSum (M := M) w' c k (tau : Real) y = 0 := by
              unfold towerReactionSum
              apply Finset.sum_eq_zero
              intro j _
              rw [hw'_val_gt k hk_gt]
              simp
            rw [hreact0]
            norm_num
      hLap := by
        intro k s hs hspos y
        by_cases hk : k <= m
        · have hfun : w' k s = w k s := by
            funext z
            rw [hw'_val_le k hk]
          rw [hwLap'_val_le k hk, hfun]
          exact hLap k s hs hspos y
        · have hfun : w' k s = fun _z : M => (0 : Real) := by
            funext z
            rw [hw'_val_gt k hk]
          rw [hwLap'_val_gt k hk, hfun]
          rw [DifferentialGeometry.Integral.Connection.heatOperatorWithDrift_zero_drift,
            DifferentialGeometry.Integral.Connection.heatOperator_eq_laplacianAt,
            DifferentialGeometry.Integral.Connection.laplacianAt_eq]
          exact DifferentialGeometry.Integral.Connection.laplacian_const
            (I := I) (G.connection s) (G.metric s) 0 y
      hw_cont := by
        intro k
        by_cases hk : k <= m
        · have hfun : (fun p : Real × M => w' k p.1 p.2) =
              (fun p : Real × M => w k p.1 p.2) := by
            funext p
            rw [hw'_val_le k hk]
          rw [hfun]
          exact hw_cont k
        · have hfun : (fun p : Real × M => w' k p.1 p.2) =
              (fun _p : Real × M => (0 : Real)) := by
            funext p
            rw [hw'_val_gt k hk]
          rw [hfun]
          exact continuousOn_const
      hw_space := by
        intro k s hs hspos y
        by_cases hk : k <= m
        · have hfun : w' k s = w k s := by
            funext z
            rw [hw'_val_le k hk]
          rw [hfun]
          exact hw_space k s hs hspos y
        · have hfun : w' k s = fun _z : M => (0 : Real) := by
            funext z
            rw [hw'_val_gt k hk]
          rw [hfun]
          exact mdifferentiableAt_const
      hw_grad := by
        intro k s hs hspos y
        by_cases hk : k <= m
        · have hfun : w' k s = w k s := by
            funext z
            rw [hw'_val_le k hk]
          simp only [hfun]
          exact hw_grad k s hs hspos y
        · have hfun : w' k s = fun _z : M => (0 : Real) := by
            funext z
            rw [hw'_val_gt k hk]
          simp only [hfun]
          refine (mdifferentiableAt_zeroSection (𝕜 := Real) (F := E)
            (E := (TangentSpace I : M -> Type _)) (x := y)).congr_of_eventuallyEq ?_
          filter_upwards with z
          exact congrArg (fun v => (⟨z, v⟩ : TotalSpace E (TangentSpace I)))
            (DifferentialGeometry.Integral.Connection.gradientFun_const (I := I) (G.metric s) 0 z) }
  have hkey : B.w m t x <= (towerConst B.c B.α m) ^ 2 * B.K ^ 2 / t ^ m :=
    B.estimate_div m htmem htpos x
  simp only [B] at hkey
  rw [hw'_val_le m le_rfl t x] at hkey
  exact hkey

end BernsteinTower

end DifferentialGeometry.PDE.RicciFlow
