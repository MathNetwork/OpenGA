import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.IteratedNablaRmTower

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

























































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
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]







omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] [CompactSpace M] in
theorem towerReactionSum_mono_const
    (w : ℕ -> Real -> M -> Real) {c c' : Real} (hcc : c <= c')
    (k : ℕ) (t : Real) (x : M) :
    towerReactionSum (M := M) w c k t x <= towerReactionSum (M := M) w c' k t x := by
  unfold towerReactionSum
  apply Finset.sum_le_sum
  intro j _
  have h1 : 0 <= Real.sqrt (w j t x) := Real.sqrt_nonneg _
  have h2 : 0 <= Real.sqrt (w (k - j) t x) := Real.sqrt_nonneg _
  have h3 : 0 <= Real.sqrt (w k t x) := Real.sqrt_nonneg _
  have hprod : 0 <= Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x) :=
    mul_nonneg (mul_nonneg h1 h2) h3
  calc c * Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x)
      = c * (Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x)) := by ring
    _ <= c' * (Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x)) :=
        mul_le_mul_of_nonneg_right hcc hprod
    _ = c' * Real.sqrt (w j t x) * Real.sqrt (w (k - j) t x) * Real.sqrt (w k t x) := by ring



omit [DecidableEq Idx] in
theorem towerLevelConst_mono {k m : ℕ} (hkm : k <= m) :
    2 * (Fintype.card Idx : Real) ^ (6 + k) <= 2 * (Fintype.card Idx : Real) ^ (6 + m) := by
  have hcard : (0 : Real) <= (Fintype.card Idx : Real) := by positivity
  have hpow : (Fintype.card Idx : Real) ^ (6 + k) <= (Fintype.card Idx : Real) ^ (6 + m) := by
    rcases Nat.eq_zero_or_pos (Fintype.card Idx) with hc0 | hcpos
    ·
      rw [hc0]
      simp only [Nat.cast_zero]
      rw [zero_pow (by omega : 6 + k ≠ 0), zero_pow (by omega : 6 + m ≠ 0)]
    ·
      have h1 : (1 : Real) <= (Fintype.card Idx : Real) := by
        have : (1 : ℕ) <= Fintype.card Idx := hcpos
        exact_mod_cast this
      exact pow_le_pow_right₀ h1 (by omega)
  linarith [mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : Real) <= 2)]
















omit [DecidableEq Idx] in
theorem bernsteinShi_solution_estimate
    {D : DifferentialGeometry.Integral.Connection.RealTimeInterval}
    (G : DifferentialGeometry.Integral.Connection.RealizedMetricFamily (I := I) (M := M) Real)
    {level : (k : ℕ) → Real → M → (Fin (4 + k) → Idx) → Real}
    {star : (k : ℕ) → Real → M → ℕ → (Fin (4 + k) → Idx) → Real}
    {w wLap : ℕ → Real → M → Real}
    (tower : IteratedRmTowerOn (D := D) level star w wLap)
    (K α T : Real)
    (hT : 0 < T) (hK : 0 < K) (hα : 0 <= α)
    (hslab : Set.Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D.regular)
    (hw_nonneg : ∀ k : ℕ, ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M, 0 <= w k t x)
    (hw0_bound : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M, w 0 t x <= K ^ 2)
    (hTK : T <= α / K)
    (hLap : ∀ k : ℕ, ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      DifferentialGeometry.Integral.Connection.heatOperatorWithDrift (I := I) G t
        (fun _y : M => (0 : TangentSpace I _y)) (w k t) x = wLap k t x)
    (hw_cont : ∀ k : ℕ, ContinuousOn (fun p : Real × M => w k p.1 p.2)
      (DifferentialGeometry.Integral.Connection.spacetimeSlab (M := M) T))
    (hw_space : ∀ k : ℕ, ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (w k t) y)
    (hw_grad : ∀ k : ℕ, ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> ∀ x : M,
      MDiffAt (T% fun y : M =>
        DifferentialGeometry.Integral.Connection.gradientFun (I := I) (G.metric t) (w k t) y) x)
    (m : ℕ) {t : Real} (htmem : t ∈ Set.Icc 0 T) (htpos : 0 < t) (x : M) :
    w m t x <=
      (towerConst (2 * (Fintype.card Idx : Real) ^ (6 + m)) α m) ^ 2 * K ^ 2 / t ^ m := by
  classical

  set c : Real := 2 * (Fintype.card Idx : Real) ^ (6 + m) with hc_def
  have hc_nonneg : (0 : Real) <= c := by rw [hc_def]; positivity

  set w' : ℕ -> Real -> M -> Real := fun k => if k <= m then w k else fun _ _ => 0 with hw'_def
  set wLap' : ℕ -> Real -> M -> Real := fun k => if k <= m then wLap k else fun _ _ => 0
    with hwLap'_def

  have hw'_le : ∀ k : ℕ, k <= m -> w' k = w k := by
    intro k hk; simp only [hw'_def, if_pos hk]
  have hw'_gt : ∀ k : ℕ, ¬ k <= m -> w' k = fun _ _ => 0 := by
    intro k hk; simp only [hw'_def, if_neg hk]
  have hwLap'_le : ∀ k : ℕ, k <= m -> wLap' k = wLap k := by
    intro k hk; simp only [hwLap'_def, if_pos hk]
  have hwLap'_gt : ∀ k : ℕ, ¬ k <= m -> wLap' k = fun _ _ => 0 := by
    intro k hk; simp only [hwLap'_def, if_neg hk]

  have hw'_val_le : ∀ k : ℕ, k <= m -> ∀ (s : Real) (y : M), w' k s y = w k s y := by
    intro k hk s y; rw [hw'_le k hk]
  have hw'_val_gt : ∀ k : ℕ, ¬ k <= m -> ∀ (s : Real) (y : M), w' k s y = 0 := by
    intro k hk s y; rw [hw'_gt k hk]
  have hwLap'_val_le : ∀ k : ℕ, k <= m -> ∀ (s : Real) (y : M), wLap' k s y = wLap k s y := by
    intro k hk s y; rw [hwLap'_le k hk]
  have hwLap'_val_gt : ∀ k : ℕ, ¬ k <= m -> ∀ (s : Real) (y : M), wLap' k s y = 0 := by
    intro k hk s y; rw [hwLap'_gt k hk]

  have hw'_nonneg : ∀ k : ℕ, ∀ s : Real, s ∈ Set.Icc 0 T -> ∀ y : M, 0 <= w' k s y := by
    intro k s hs y
    by_cases hk : k <= m
    · rw [hw'_val_le k hk]; exact hw_nonneg k s hs y
    · rw [hw'_val_gt k hk]


  have hreact_eq : ∀ k : ℕ, k <= m -> ∀ (s : Real) (y : M),
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

  set B : BernsteinTower (I := I) G :=
    { D := D
      w := w'
      wLap := wLap'
      c := c
      K := K
      α := α
      T := T
      hT := hT
      hc := hc_nonneg
      hK := hK
      hα := hα
      hslab := hslab
      hregular := hregular
      hw_nonneg := hw'_nonneg
      hw0_bound := by
        intro s hs y
        rw [hw'_val_le 0 (Nat.zero_le m)]
        exact hw0_bound s hs y
      hTK := hTK
      hheat := by

        intro k τ y
        rcases lt_trichotomy k m with hlt | heq | hgt
        ·
          have hk_le : k <= m := le_of_lt hlt
          have hk1_le : k + 1 <= m := hlt
          obtain ⟨d, hderiv, hle⟩ :=
            iteratedRmTower_heatBound tower k τ y
          refine ⟨d, ?_, ?_⟩
          ·
            have : (fun s : Real => w' k s y) = (fun s : Real => w k s y) := by
              funext s; rw [hw'_val_le k hk_le]
            rw [this]; exact hderiv
          ·
            rw [hwLap'_val_le k hk_le, hw'_val_le (k + 1) hk1_le,
              hreact_eq k hk_le]
            have hmono : towerReactionSum (M := M) w
                  (2 * (Fintype.card Idx : Real) ^ (6 + k)) k (τ : Real) y <=
                towerReactionSum (M := M) w c k (τ : Real) y :=
              towerReactionSum_mono_const w (towerLevelConst_mono (Idx := Idx) hk_le)
                k (τ : Real) y
            linarith [hle, hmono]
        ·
          subst heq
          have hk_le : k <= k := le_refl k
          have hk1_gt : ¬ k + 1 <= k := by omega
          obtain ⟨d, hderiv, hle⟩ :=
            iteratedRmTower_heatBound tower k τ y

          rw [← hc_def] at hle
          refine ⟨d, ?_, ?_⟩
          · have : (fun s : Real => w' k s y) = (fun s : Real => w k s y) := by
              funext s; rw [hw'_val_le k hk_le]
            rw [this]; exact hderiv
          · rw [hwLap'_val_le k hk_le, hw'_val_gt (k + 1) hk1_gt,
              hreact_eq k hk_le]



            have hnn : 0 <= w (k + 1) (τ : Real) y := by
              rw [tower.wDef (k + 1) (τ : Real) y]
              exact compNormSqMulti_nonneg _
            nlinarith [hle, hnn]
        ·
          have hk_gt : ¬ k <= m := by omega
          have hk1_gt : ¬ k + 1 <= m := by omega
          refine ⟨0, ?_, ?_⟩
          · have : (fun s : Real => w' k s y) = (fun _s : Real => (0 : Real)) := by
              funext s; rw [hw'_val_gt k hk_gt]
            rw [this]; exact hasDerivWithinAt_const _ _ _
          · rw [hwLap'_val_gt k hk_gt, hw'_val_gt (k + 1) hk1_gt]

            have hreact0 : towerReactionSum (M := M) w' c k (τ : Real) y = 0 := by
              unfold towerReactionSum
              apply Finset.sum_eq_zero
              intro j _
              rw [hw'_val_gt k hk_gt]
              simp
            rw [hreact0]; norm_num
      hLap := by
        intro k s hs hspos y
        by_cases hk : k <= m
        ·
          have hfun : (w' k s) = (w k s) := by funext z; rw [hw'_val_le k hk]
          rw [hwLap'_val_le k hk, hfun]
          exact hLap k s hs hspos y
        ·
          have hfun : (w' k s) = (fun _z : M => (0 : Real)) := by
            funext z; rw [hw'_val_gt k hk]
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
            funext p; rw [hw'_val_le k hk]
          rw [hfun]; exact hw_cont k
        · have hfun : (fun p : Real × M => w' k p.1 p.2) =
              (fun _p : Real × M => (0 : Real)) := by
            funext p; rw [hw'_val_gt k hk]
          rw [hfun]; exact continuousOn_const
      hw_space := by
        intro k s hs hspos y
        by_cases hk : k <= m
        · have hfun : (w' k s) = (w k s) := by funext z; rw [hw'_val_le k hk]
          rw [hfun]; exact hw_space k s hs hspos y
        · have hfun : (w' k s) = (fun _z : M => (0 : Real)) := by
            funext z; rw [hw'_val_gt k hk]
          rw [hfun]; exact mdifferentiableAt_const
      hw_grad := by
        intro k s hs hspos y
        by_cases hk : k <= m
        · have hfun : (w' k s) = (w k s) := by funext z; rw [hw'_val_le k hk]
          simp only [hfun]; exact hw_grad k s hs hspos y
        · have hfun : (w' k s) = (fun _z : M => (0 : Real)) := by
            funext z; rw [hw'_val_gt k hk]
          simp only [hfun]

          refine (mdifferentiableAt_zeroSection (𝕜 := Real) (F := E)
            (E := (TangentSpace I : M -> Type _)) (x := y)).congr_of_eventuallyEq ?_
          filter_upwards with z
          exact congrArg (fun v => (⟨z, v⟩ : TotalSpace E (TangentSpace I)))
            (DifferentialGeometry.Integral.Connection.gradientFun_const (I := I) (G.metric s) 0 z) }
    with hB_def

  have hkey : B.w m t x <= (towerConst B.c B.α m) ^ 2 * B.K ^ 2 / t ^ m :=
    B.estimate_div m htmem htpos x

  simp only [hB_def] at hkey

  rw [hw'_val_le m (le_refl m) t x] at hkey
  exact hkey

end DifferentialGeometry.PDE.RicciFlow
