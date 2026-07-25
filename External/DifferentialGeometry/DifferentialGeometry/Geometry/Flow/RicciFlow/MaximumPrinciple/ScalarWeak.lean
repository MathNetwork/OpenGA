import DifferentialGeometry.Geometry.Curvature.Realized.Operators
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false












namespace DifferentialGeometry.Integral.Connection

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


def spacetimeSlab (T : Real) : Set (Real × M) :=
  Set.Icc 0 T ×ˢ Set.univ


def parabolicOperatorWithDrift
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (t : Real) (x : M) : Real :=
  derivWithin (fun s : Real => u s x) (Set.Icc 0 T) t -
    heatOperatorWithDrift (I := I) G t (X t) (u t) x

@[simp] theorem parabolicOperatorWithDrift_eq
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (t : Real) (x : M) :
    parabolicOperatorWithDrift (I := I) G T X u t x =
      derivWithin (fun s : Real => u s x) (Set.Icc 0 T) t -
        heatOperatorWithDrift (I := I) G t (X t) (u t) x := by
  rfl


theorem parabolic_const_sub
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (C t : Real) (x : M)
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t)
    (hu_time : DifferentiableWithinAt Real
      (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hu_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hu_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (u t) y) x) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => C - u s y) t x =
      - parabolicOperatorWithDrift (I := I) G T X u t x := by
  unfold parabolicOperatorWithDrift
  have htime :
      derivWithin (fun s : Real => C - u s x) (Set.Icc 0 T) t =
        - derivWithin (fun s : Real => u s x) (Set.Icc 0 T) t := by
    have hconst : DifferentiableWithinAt Real
        (fun _s : Real => C) (Set.Icc 0 T) t :=
      differentiableWithinAt_const C
    rw [derivWithin_fun_sub hconst hu_time]
    have hconst_deriv :
        derivWithin (fun _s : Real => C) (Set.Icc 0 T) t = 0 := by
      exact (hasDerivWithinAt_const
        (x := t) (s := Set.Icc 0 T) (c := C)).derivWithin huniq
    rw [hconst_deriv]
    ring
  have hsub_space : forall y : M,
      MDifferentiableAt I 𝓘(Real, Real) (fun z : M => u t z - C) y := by
    intro y
    exact (hu_space y).sub mdifferentiableAt_const
  have hsub_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (fun z : M => u t z - C) y) x := by
    have hplain :
        (fun y : M =>
          gradientFun (I := I) (G.metric t) (fun z : M => u t z - C) y) =
        (fun y : M => gradientFun (I := I) (G.metric t) (u t) y) := by
      funext y
      calc
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - C) y =
          gradientFun (I := I) (G.metric t) (u t) y -
            gradientFun (I := I) (G.metric t) (fun _ : M => C) y := by
            exact gradientFun_sub (I := I) (G.metric t)
              (hu_space y) mdifferentiableAt_const
        _ = gradientFun (I := I) (G.metric t) (u t) y := by
            rw [gradientFun_const]
            simp
    have hsection :
        (T% fun y : M =>
          gradientFun (I := I) (G.metric t) (fun z : M => u t z - C) y) =
        (T% fun y : M => gradientFun (I := I) (G.metric t) (u t) y) := by
      funext y
      simpa using congrFun hplain y
    rw [hsection]
    exact hu_grad
  have hheat_sub :
      heatOperatorWithDrift (I := I) G t (X t) (fun y : M => u t y - C) x =
        heatOperatorWithDrift (I := I) G t (X t) (u t) x :=
    heatOperatorWithDrift_sub_const (I := I) G t (X t) C hu_space x
  have hheat_scale :
      heatOperatorWithDrift (I := I) G t (X t)
          ((-1 : Real) • fun y : M => u t y - C) x =
        (-1 : Real) *
          heatOperatorWithDrift (I := I) G t (X t) (fun y : M => u t y - C) x :=
    heatOperatorWithDrift_const_smul (I := I) G t (X t) (-1)
      (f := fun y : M => u t y - C) hsub_space hsub_grad
  have hheat :
      heatOperatorWithDrift (I := I) G t (X t)
          (fun y : M => C - u t y) x =
        - heatOperatorWithDrift (I := I) G t (X t) (u t) x := by
    have hfun :
        (fun y : M => C - u t y) =
          ((-1 : Real) • fun y : M => u t y - C) := by
      funext y
      simp
    rw [hfun, hheat_scale, hheat_sub]
    ring
  rw [htime, hheat]
  ring





theorem reaction_difference_lower_bound_on_negative_region
    {uval cval Fu Fc L : Real}
    (hlip : |Fu - Fc| <= L * |uval - cval|)
    (hneg : uval - cval < 0) :
    L * (uval - cval) <= Fu - Fc := by
  have hlow_abs : -(L * |uval - cval|) <= Fu - Fc := by
    exact le_trans (neg_le_neg hlip) (neg_abs_le (Fu - Fc))
  have hvabs : |uval - cval| = -(uval - cval) := abs_of_neg hneg
  calc
    L * (uval - cval) = -(L * |uval - cval|) := by
      rw [hvabs]
      ring
    _ <= Fu - Fc := hlow_abs



theorem negative_region_parabolic_lower_bound
    {uval cval Pu Pv cderiv Fu Fc L : Real}
    (hsuper : Fu <= Pu)
    (hode : cderiv = Fc)
    (hsub : Pv = Pu - cderiv)
    (hlip : |Fu - Fc| <= L * |uval - cval|)
    (hneg : uval - cval < 0) :
    L * (uval - cval) <= Pv := by
  have hlow : L * (uval - cval) <= Fu - Fc :=
    reaction_difference_lower_bound_on_negative_region hlip hneg
  have hupper : Fu - Fc <= Pv := by
    calc
      Fu - Fc <= Pu - cderiv := by
        rw [hode]
        exact sub_le_sub_right hsuper Fc
      _ = Pv := hsub.symm
  exact le_trans hlow hupper











theorem parabolic_sub_time_curve_identity
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (t : Real) (_ht : t ∈ Set.Icc 0 T)
    (hu_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (x : M)
    (hu : DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hc : DifferentiableWithinAt Real c (Set.Icc 0 T) t) :
    parabolicOperatorWithDrift (I := I) G T X (fun s y => u s y - c s) t x =
      parabolicOperatorWithDrift (I := I) G T X u t x -
        derivWithin c (Set.Icc 0 T) t := by
  unfold parabolicOperatorWithDrift
  have htime :
      derivWithin (fun s : Real => u s x - c s) (Set.Icc 0 T) t =
        derivWithin (fun s : Real => u s x) (Set.Icc 0 T) t -
          derivWithin c (Set.Icc 0 T) t := by
    exact derivWithin_fun_sub hu hc
  have hheat :
      heatOperatorWithDrift (I := I) G t (X t) (fun y : M => u t y - c t) x =
        heatOperatorWithDrift (I := I) G t (X t) (u t) x := by
    exact heatOperatorWithDrift_sub_const (I := I) G t (X t) (c t) hu_space x
  rw [htime, hheat]
  ring






theorem parabolic_exp_rescale_identity
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T L : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (v : Real -> M -> Real)
    (t : Real) (_ht : t ∈ Set.Icc 0 T)
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t)
    (hv_space : forall y : M, MDifferentiableAt I 𝓘(Real, Real) (v t) y)
    (x : M)
    (hv_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (v t) y) x)
    (hv : DifferentiableWithinAt Real (fun s : Real => v s x) (Set.Icc 0 T) t)
    (hscale : DifferentiableWithinAt Real (fun s : Real => Real.exp (-L * s))
      (Set.Icc 0 T) t) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => Real.exp (-L * s) * v s y) t x =
      Real.exp (-L * t) *
        (parabolicOperatorWithDrift (I := I) G T X v t x - L * v t x) := by
  unfold parabolicOperatorWithDrift
  have hlinear_diff :
      DifferentiableWithinAt Real (fun s : Real => -L * s) (Set.Icc 0 T) t := by
    simpa using
      (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul (-L)
  have hlinear_deriv :
      derivWithin (fun s : Real => -L * s) (Set.Icc 0 T) t = -L := by
    have hid :
        derivWithin (fun s : Real => s) (Set.Icc 0 T) t = 1 := by
      exact derivWithin_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t) huniq
    rw [derivWithin_const_mul (-L)
      (d := fun s : Real => s) (s := Set.Icc 0 T) (x := t) differentiableWithinAt_id]
    rw [hid]
    ring
  have hscale_deriv :
      derivWithin (fun s : Real => Real.exp (-L * s)) (Set.Icc 0 T) t =
        -L * Real.exp (-L * t) := by
    rw [derivWithin_exp hlinear_diff huniq]
    rw [hlinear_deriv]
    ring
  have htime :
      derivWithin (fun s : Real => Real.exp (-L * s) * v s x) (Set.Icc 0 T) t =
        (-L * Real.exp (-L * t)) * v t x +
          Real.exp (-L * t) * derivWithin (fun s : Real => v s x) (Set.Icc 0 T) t := by
    rw [derivWithin_fun_mul hscale hv]
    rw [hscale_deriv]
  have hheat :
      heatOperatorWithDrift (I := I) G t (X t)
          (fun y : M => Real.exp (-L * t) * v t y) x =
        Real.exp (-L * t) * heatOperatorWithDrift (I := I) G t (X t) (v t) x := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      heatOperatorWithDrift_const_smul (I := I) G t (X t) (Real.exp (-L * t))
        (f := v t) hv_space hv_grad
  rw [htime, hheat]
  ring




private theorem spacetimeSlab_isCompact
    [CompactSpace M] (T : Real) :
    IsCompact (spacetimeSlab (M := M) T) := by
  unfold spacetimeSlab
  exact isCompact_Icc.prod isCompact_univ



private theorem derivWithin_nonpos_at_Icc_min_of_pos
    {φ : Real -> Real} {T t : Real}
    (hmin : IsMinOn φ (Set.Icc 0 T) t)
    (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
    (_hφ : DifferentiableWithinAt Real φ (Set.Icc 0 T) t) :
    derivWithin φ (Set.Icc 0 T) t <= 0 := by
  have hlocal : IsLocalMinOn φ (Set.Icc 0 T) t := hmin.localize
  have hdir : (0 : Real) - t ∈ posTangentConeAt (Set.Icc 0 T) t := by
    have hseg : segment Real t 0 ⊆ Set.Icc 0 T := by
      rw [segment_symm, segment_eq_Icc ht.1]
      intro y hy
      exact ⟨hy.1, hy.2.trans ht.2⟩
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonneg :
      (0 : Real) <=
        (fderivWithin Real φ (Set.Icc 0 T) t : Real →L[Real] Real) (0 - t) :=
    hlocal.fderivWithin_nonneg hdir
  have hlin :
      (fderivWithin Real φ (Set.Icc 0 T) t : Real →L[Real] Real) (0 - t) =
        (0 - t) * derivWithin φ (Set.Icc 0 T) t := by
    rw [← fderivWithin_derivWithin (𝕜 := Real) (f := φ) (s := Set.Icc 0 T) (x := t)]
    simpa [smul_eq_mul] using
      ((fderivWithin Real φ (Set.Icc 0 T) t : Real →L[Real] Real).map_smul
        (0 - t) (1 : Real))
  have htneg : (0 : Real) - t < 0 := sub_neg.mpr htpos
  rw [hlin] at hnonneg
  exact nonpos_of_mul_nonneg_right hnonneg htneg


omit [TopologicalSpace M] in
private theorem derivWithin_add_eps_mul_time
    {w : Real -> M -> Real} {T t ε : Real} {x : M}
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t)
    (hw : DifferentiableWithinAt Real (fun s : Real => w s x) (Set.Icc 0 T) t) :
    derivWithin (fun s : Real => w s x + ε * s) (Set.Icc 0 T) t =
      derivWithin (fun s : Real => w s x) (Set.Icc 0 T) t + ε := by
  have hlinear :
      DifferentiableWithinAt Real (fun s : Real => ε * s) (Set.Icc 0 T) t := by
    simpa using
      (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul ε
  have hderiv_linear :
      derivWithin (fun s : Real => ε * s) (Set.Icc 0 T) t = ε := by
    rw [derivWithin_const_mul ε
      (d := fun s : Real => s) (s := Set.Icc 0 T) (x := t) differentiableWithinAt_id]
    rw [derivWithin_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t) huniq]
    ring
  rw [derivWithin_fun_add hw hlinear]
  rw [hderiv_linear]


theorem strict_barrier_nonnegative_of_positive_time
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (_hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (w : Real -> M -> Real)
    (hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2) (spacetimeSlab (M := M) T))
    (hw0 : forall x : M, 0 <= w 0 x)
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real (fun s : Real => w s x) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real) (w t) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x)
    (hnegative : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x := by
  classical
  have hbarrier_nonneg :
      forall ε : Real, 0 < ε ->
        forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
          0 <= w t x + ε * t := by
    intro ε hε
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨tb, htb, xb, hbneg⟩
    let Φ : Real × M -> Real := fun p => w p.1 p.2 + ε * p.1
    have hΦ_cont : ContinuousOn Φ (spacetimeSlab (M := M) T) := by
      have hlinear :
          ContinuousOn (fun p : Real × M => ε * p.1) (spacetimeSlab (M := M) T) :=
        (continuous_const.mul continuous_fst).continuousOn
      exact hw_cont.add hlinear
    have hslab_compact : IsCompact (spacetimeSlab (M := M) T) :=
      spacetimeSlab_isCompact (M := M) T
    have hslab_nonempty : (spacetimeSlab (M := M) T).Nonempty :=
      ⟨(tb, xb), ⟨htb, trivial⟩⟩
    obtain ⟨p0, hp0, hp0min⟩ :=
      hslab_compact.exists_isMinOn hslab_nonempty hΦ_cont
    rcases p0 with ⟨t0, x0⟩
    have hp0_time : t0 ∈ Set.Icc 0 T := hp0.1
    have hΦ_min_bad : Φ (t0, x0) <= Φ (tb, xb) :=
      hp0min (show (tb, xb) ∈ spacetimeSlab (M := M) T from ⟨htb, trivial⟩)
    have hΦ0_neg : Φ (t0, x0) < 0 := lt_of_le_of_lt hΦ_min_bad hbneg
    have ht0_ne_zero : t0 ≠ 0 := by
      intro ht0
      have hnonneg0 : 0 <= Φ (t0, x0) := by
        simp [Φ, ht0, hw0 x0]
      exact not_lt_of_ge hnonneg0 hΦ0_neg
    have ht0_pos : 0 < t0 := lt_of_le_of_ne hp0_time.1 (Ne.symm ht0_ne_zero)
    have hT_pos : 0 < T := lt_of_lt_of_le ht0_pos hp0_time.2
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t0 :=
      (uniqueDiffOn_Icc hT_pos).uniqueDiffWithinAt hp0_time
    have htime_min : IsMinOn (fun s : Real => w s x0 + ε * s) (Set.Icc 0 T) t0 := by
      intro s hs
      exact hp0min (show (s, x0) ∈ spacetimeSlab (M := M) T from ⟨hs, trivial⟩)
    have htime_diff :
        DifferentiableWithinAt Real (fun s : Real => w s x0 + ε * s)
          (Set.Icc 0 T) t0 := by
      exact (hw_time t0 hp0_time x0).add
        ((differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t0)).const_mul ε)
    have hbarrier_deriv_nonpos :
        derivWithin (fun s : Real => w s x0 + ε * s) (Set.Icc 0 T) t0 <= 0 :=
      derivWithin_nonpos_at_Icc_min_of_pos htime_min hp0_time ht0_pos htime_diff
    have hderiv_eq :
      derivWithin (fun s : Real => w s x0 + ε * s) (Set.Icc 0 T) t0 =
        derivWithin (fun s : Real => w s x0) (Set.Icc 0 T) t0 + ε :=
      derivWithin_add_eps_mul_time (M := M) huniq (hw_time t0 hp0_time x0)
    have hw_deriv_le : derivWithin (fun s : Real => w s x0) (Set.Icc 0 T) t0 <= -ε := by
      linarith
    have hw_t0_neg : w t0 x0 < 0 := by
      have hεt_nonneg : 0 <= ε * t0 := mul_nonneg (le_of_lt hε) hp0_time.1
      nlinarith [hΦ0_neg, hεt_nonneg]
    have hspatial_min : IsLocalMin (w t0) x0 := by
      unfold IsLocalMin IsMinFilter
      exact Filter.Eventually.of_forall fun y => by
        have hymin : Φ (t0, x0) <= Φ (t0, y) :=
          hp0min (show (t0, y) ∈ spacetimeSlab (M := M) T from ⟨hp0_time, trivial⟩)
        dsimp [Φ] at hymin ⊢
        linarith
    have hheat_nonneg :
        0 <= heatOperatorWithDrift (I := I) G t0 (X t0) (w t0) x0 :=
      heatOperatorWithDrift_at_spatial_min_nonneg (I := I) G t0 (X t0)
        hspatial_min (hw_mdiff t0 hp0_time x0)
        (Filter.Eventually.of_forall fun y => hw_mdiff t0 hp0_time y)
        (hw_grad t0 hp0_time x0)
    have hP_neg :
        parabolicOperatorWithDrift (I := I) G T X w t0 x0 < 0 := by
      unfold parabolicOperatorWithDrift
      linarith
    exact not_lt_of_ge (hnegative t0 hp0_time ht0_pos x0 hw_t0_neg) hP_neg
  intro t ht x
  by_contra hnot
  have hw_neg : w t x < 0 := lt_of_not_ge hnot
  by_cases ht_zero : t = 0
  · exact not_lt_of_ge (by simpa [ht_zero] using hw0 x) hw_neg
  · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_zero)
    let ε : Real := -(w t x) / (2 * t)
    have hε_pos : 0 < ε := by
      exact div_pos (neg_pos.mpr hw_neg) (mul_pos two_pos ht_pos)
    have hbarrier := hbarrier_nonneg ε hε_pos t ht x
    have hε_mul : ε * t = -(w t x) / 2 := by
      dsimp [ε]
      field_simp [ht_zero]
    have hbarrier_neg : w t x + ε * t < 0 := by
      rw [hε_mul]
      linarith
    exact not_lt_of_ge hbarrier hbarrier_neg







theorem strict_barrier_posReg
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (_hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (w : Real -> M -> Real)
    (hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2) (spacetimeSlab (M := M) T))
    (hw0 : forall x : M, 0 <= w 0 x)
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, DifferentiableWithinAt Real (fun s : Real => w s x) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real) (w t) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x)
    (hnegative : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x := by
  classical
  have hbarrier_nonneg :
      forall ε : Real, 0 < ε ->
        forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
          0 <= w t x + ε * t := by
    intro ε hε
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨tb, htb, xb, hbneg⟩
    let Φ : Real × M -> Real := fun p => w p.1 p.2 + ε * p.1
    have hΦ_cont : ContinuousOn Φ (spacetimeSlab (M := M) T) := by
      have hlinear :
          ContinuousOn (fun p : Real × M => ε * p.1) (spacetimeSlab (M := M) T) :=
        (continuous_const.mul continuous_fst).continuousOn
      exact hw_cont.add hlinear
    have hslab_compact : IsCompact (spacetimeSlab (M := M) T) :=
      spacetimeSlab_isCompact (M := M) T
    have hslab_nonempty : (spacetimeSlab (M := M) T).Nonempty :=
      ⟨(tb, xb), ⟨htb, trivial⟩⟩
    obtain ⟨p0, hp0, hp0min⟩ :=
      hslab_compact.exists_isMinOn hslab_nonempty hΦ_cont
    rcases p0 with ⟨t0, x0⟩
    have hp0_time : t0 ∈ Set.Icc 0 T := hp0.1
    have hΦ_min_bad : Φ (t0, x0) <= Φ (tb, xb) :=
      hp0min (show (tb, xb) ∈ spacetimeSlab (M := M) T from ⟨htb, trivial⟩)
    have hΦ0_neg : Φ (t0, x0) < 0 := lt_of_le_of_lt hΦ_min_bad hbneg
    have ht0_ne_zero : t0 ≠ 0 := by
      intro ht0
      have hnonneg0 : 0 <= Φ (t0, x0) := by
        simp [Φ, ht0, hw0 x0]
      exact not_lt_of_ge hnonneg0 hΦ0_neg
    have ht0_pos : 0 < t0 := lt_of_le_of_ne hp0_time.1 (Ne.symm ht0_ne_zero)
    have hT_pos : 0 < T := lt_of_lt_of_le ht0_pos hp0_time.2
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t0 :=
      (uniqueDiffOn_Icc hT_pos).uniqueDiffWithinAt hp0_time
    have htime_min : IsMinOn (fun s : Real => w s x0 + ε * s) (Set.Icc 0 T) t0 := by
      intro s hs
      exact hp0min (show (s, x0) ∈ spacetimeSlab (M := M) T from ⟨hs, trivial⟩)
    have htime_diff :
        DifferentiableWithinAt Real (fun s : Real => w s x0 + ε * s)
          (Set.Icc 0 T) t0 := by
      exact (hw_time t0 hp0_time ht0_pos x0).add
        ((differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t0)).const_mul ε)
    have hbarrier_deriv_nonpos :
        derivWithin (fun s : Real => w s x0 + ε * s) (Set.Icc 0 T) t0 <= 0 :=
      derivWithin_nonpos_at_Icc_min_of_pos htime_min hp0_time ht0_pos htime_diff
    have hderiv_eq :
      derivWithin (fun s : Real => w s x0 + ε * s) (Set.Icc 0 T) t0 =
        derivWithin (fun s : Real => w s x0) (Set.Icc 0 T) t0 + ε :=
      derivWithin_add_eps_mul_time (M := M) huniq (hw_time t0 hp0_time ht0_pos x0)
    have hw_deriv_le : derivWithin (fun s : Real => w s x0) (Set.Icc 0 T) t0 <= -ε := by
      linarith
    have hw_t0_neg : w t0 x0 < 0 := by
      have hεt_nonneg : 0 <= ε * t0 := mul_nonneg (le_of_lt hε) hp0_time.1
      nlinarith [hΦ0_neg, hεt_nonneg]
    have hspatial_min : IsLocalMin (w t0) x0 := by
      unfold IsLocalMin IsMinFilter
      exact Filter.Eventually.of_forall fun y => by
        have hymin : Φ (t0, x0) <= Φ (t0, y) :=
          hp0min (show (t0, y) ∈ spacetimeSlab (M := M) T from ⟨hp0_time, trivial⟩)
        dsimp [Φ] at hymin ⊢
        linarith
    have hheat_nonneg :
        0 <= heatOperatorWithDrift (I := I) G t0 (X t0) (w t0) x0 :=
      heatOperatorWithDrift_at_spatial_min_nonneg (I := I) G t0 (X t0)
        hspatial_min (hw_mdiff t0 hp0_time ht0_pos x0)
        (Filter.Eventually.of_forall fun y => hw_mdiff t0 hp0_time ht0_pos y)
        (hw_grad t0 hp0_time ht0_pos x0)
    have hP_neg :
        parabolicOperatorWithDrift (I := I) G T X w t0 x0 < 0 := by
      unfold parabolicOperatorWithDrift
      linarith
    exact not_lt_of_ge (hnegative t0 hp0_time ht0_pos x0 hw_t0_neg) hP_neg
  intro t ht x
  by_contra hnot
  have hw_neg : w t x < 0 := lt_of_not_ge hnot
  by_cases ht_zero : t = 0
  · exact not_lt_of_ge (by simpa [ht_zero] using hw0 x) hw_neg
  · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht_zero)
    let ε : Real := -(w t x) / (2 * t)
    have hε_pos : 0 < ε := by
      exact div_pos (neg_pos.mpr hw_neg) (mul_pos two_pos ht_pos)
    have hbarrier := hbarrier_nonneg ε hε_pos t ht x
    have hε_mul : ε * t = -(w t x) / 2 := by
      dsimp [ε]
      field_simp [ht_zero]
    have hbarrier_neg : w t x + ε * t < 0 := by
      rw [hε_mul]
      linarith
    exact not_lt_of_ge hbarrier hbarrier_neg


theorem strict_barrier_nonnegative
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (w : Real -> M -> Real)
    (hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2) (spacetimeSlab (M := M) T))
    (hw0 : forall x : M, 0 <= w 0 x)
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real (fun s : Real => w s x) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real) (w t) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x)
    (hnegative : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
  strict_barrier_nonnegative_of_positive_time (I := I) G T hT X w
    hw_cont hw0 hw_time hw_mdiff hw_grad
    (fun t ht _htpos x hwneg => hnegative t ht x hwneg)







theorem scalar_wmp_sub_const_of_parabolic_nonpos
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (C : Real)
    (hw_cont : ContinuousOn
      (fun p : Real × M => C - u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => C - u s x) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => C - u t y) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => C - u t z) y) x)
    (hinit : forall x : M, u 0 x <= C)
    (hsub : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M,
        parabolicOperatorWithDrift (I := I) G T X u t x <= 0)
    (hoperator_neg : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
        (fun s y => C - u s y) t x =
      - parabolicOperatorWithDrift (I := I) G T X u t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, u t x <= C := by
  let w : Real -> M -> Real := fun t x => C - u t x
  have hw0 : forall x : M, 0 <= w 0 x := by
    intro x
    exact sub_nonneg.mpr (hinit x)
  have hnegative : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht htpos x _hwneg
    rw [hoperator_neg t ht x]
    exact neg_nonneg.mpr (hsub t ht htpos x)
  have hw_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
    strict_barrier_nonnegative_of_positive_time (I := I) G T hT X w
      (by simpa [w] using hw_cont) hw0
      (by simpa [w] using hw_time)
      (by simpa [w] using hw_mdiff)
      (by simpa [w] using hw_grad)
      hnegative
  intro t ht x
  exact sub_nonneg.mp (by simpa [w] using hw_nonneg t ht x)



theorem scalar_sub_const_posReg
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (C : Real)
    (hw_cont : ContinuousOn
      (fun p : Real × M => C - u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => C - u s x) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => C - u t y) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => C - u t z) y) x)
    (hinit : forall x : M, u 0 x <= C)
    (hsub : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M,
        parabolicOperatorWithDrift (I := I) G T X u t x <= 0)
    (hoperator_neg : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
        (fun s y => C - u s y) t x =
      - parabolicOperatorWithDrift (I := I) G T X u t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, u t x <= C := by
  let w : Real -> M -> Real := fun t x => C - u t x
  have hw0 : forall x : M, 0 <= w 0 x := by
    intro x
    exact sub_nonneg.mpr (hinit x)
  have hnegative : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht htpos x _hwneg
    rw [hoperator_neg t ht htpos x]
    exact neg_nonneg.mpr (hsub t ht htpos x)
  have hw_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
    strict_barrier_posReg (I := I) G T hT X w
      (by simpa [w] using hw_cont) hw0
      (by simpa [w] using hw_time)
      (by simpa [w] using hw_mdiff)
      (by simpa [w] using hw_grad)
      hnegative
  intro t ht x
  exact sub_nonneg.mp (by simpa [w] using hw_nonneg t ht x)








theorem scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_values
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (L : Real)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-L * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => Real.exp (-L * s) * (u s x - c s)) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-L * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-L * t) * (u t z - c t)) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hlip : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      |F (u t x) t - F (c t) t| <= L * |u t x - c t|)
    (hsubCalc : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - c s) t x =
        parabolicOperatorWithDrift (I := I) G T X u t x -
          derivWithin c (Set.Icc 0 T) t)
    (hexpCalc : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
          (fun s y => Real.exp (-L * s) * (u s y - c s)) t x =
        Real.exp (-L * t) *
          (parabolicOperatorWithDrift (I := I) G T X
              (fun s y => u s y - c s) t x - L * (u t x - c t))) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  let v : Real -> M -> Real := fun t x => u t x - c t
  let w : Real -> M -> Real := fun t x => Real.exp (-L * t) * v t x
  have hw0 : forall x : M, 0 <= w 0 x := by
    intro x
    have hv0 : 0 <= v 0 x := by
      exact sub_nonneg.mpr (hinit x)
    simpa [w, v] using hv0
  have hnegative : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht x hwneg
    have hexppos : 0 < Real.exp (-L * t) := Real.exp_pos _
    have hvneg : v t x < 0 := by
      by_contra hnonneg
      have hvnonneg : 0 <= v t x := le_of_not_gt hnonneg
      have hprod : 0 <= Real.exp (-L * t) * v t x :=
        mul_nonneg (le_of_lt hexppos) hvnonneg
      exact not_le_of_gt (by simpa [w] using hwneg) hprod
    have hPvLower :
        L * (u t x - c t) <=
          parabolicOperatorWithDrift (I := I) G T X v t x := by
      exact negative_region_parabolic_lower_bound
        (hsuper t ht x)
        (hode t ht)
        (by simpa [v] using hsubCalc t ht x)
        (hlip t ht x)
        (by simpa [v] using hvneg)
    have hregion :
        0 <= parabolicOperatorWithDrift (I := I) G T X v t x - L * v t x := by
      exact sub_nonneg.mpr (by simpa [v] using hPvLower)
    calc
      0 <= Real.exp (-L * t) *
          (parabolicOperatorWithDrift (I := I) G T X v t x - L * v t x) := by
        exact mul_nonneg (le_of_lt hexppos) hregion
      _ = parabolicOperatorWithDrift (I := I) G T X w t x := by
        rw [← hexpCalc t ht x]
  have hw_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
    strict_barrier_nonnegative (I := I) G T hT X w
      (by simpa [w, v] using hw_cont) hw0
      (by simpa [w, v] using hw_time)
      (by simpa [w, v] using hw_mdiff) (by simpa [w, v] using hw_grad)
      hnegative
  intro t ht x
  have hvnonneg : 0 <= v t x := by
    by_contra hneg'
    have hvneg : v t x < 0 := lt_of_not_ge hneg'
    have hprodneg : w t x < 0 := by
      exact mul_neg_of_pos_of_neg (Real.exp_pos _) hvneg
    exact not_lt_of_ge (hw_nonneg t ht x) hprodneg
  exact sub_nonneg.mp (by simpa [v] using hvnonneg)




theorem scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_values_of_positive_time
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (L : Real)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-L * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => Real.exp (-L * s) * (u s x - c s)) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-L * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-L * t) * (u t z - c t)) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hlip : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      |F (u t x) t - F (c t) t| <= L * |u t x - c t|)
    (hsubCalc : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - c s) t x =
        parabolicOperatorWithDrift (I := I) G T X u t x -
          derivWithin c (Set.Icc 0 T) t)
    (hexpCalc : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
          (fun s y => Real.exp (-L * s) * (u s y - c s)) t x =
        Real.exp (-L * t) *
          (parabolicOperatorWithDrift (I := I) G T X
              (fun s y => u s y - c s) t x - L * (u t x - c t))) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  let v : Real -> M -> Real := fun t x => u t x - c t
  let w : Real -> M -> Real := fun t x => Real.exp (-L * t) * v t x
  have hw0 : forall x : M, 0 <= w 0 x := by
    intro x
    have hv0 : 0 <= v 0 x := by
      exact sub_nonneg.mpr (hinit x)
    simpa [w, v] using hv0
  have hnegative : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht htpos x hwneg
    have hexppos : 0 < Real.exp (-L * t) := Real.exp_pos _
    have hvneg : v t x < 0 := by
      by_contra hnonneg
      have hvnonneg : 0 <= v t x := le_of_not_gt hnonneg
      have hprod : 0 <= Real.exp (-L * t) * v t x :=
        mul_nonneg (le_of_lt hexppos) hvnonneg
      exact not_le_of_gt (by simpa [w] using hwneg) hprod
    have hPvLower :
        L * (u t x - c t) <=
          parabolicOperatorWithDrift (I := I) G T X v t x := by
      exact negative_region_parabolic_lower_bound
        (hsuper t ht htpos x)
        (hode t ht)
        (by simpa [v] using hsubCalc t ht x)
        (hlip t ht x)
        (by simpa [v] using hvneg)
    have hregion :
        0 <= parabolicOperatorWithDrift (I := I) G T X v t x - L * v t x := by
      exact sub_nonneg.mpr (by simpa [v] using hPvLower)
    calc
      0 <= Real.exp (-L * t) *
          (parabolicOperatorWithDrift (I := I) G T X v t x - L * v t x) := by
        exact mul_nonneg (le_of_lt hexppos) hregion
      _ = parabolicOperatorWithDrift (I := I) G T X w t x := by
        rw [← hexpCalc t ht x]
  have hw_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
    strict_barrier_nonnegative_of_positive_time (I := I) G T hT X w
      (by simpa [w, v] using hw_cont) hw0
      (by simpa [w, v] using hw_time)
      (by simpa [w, v] using hw_mdiff) (by simpa [w, v] using hw_grad)
      hnegative
  intro t ht x
  have hvnonneg : 0 <= v t x := by
    by_contra hneg'
    have hvneg : v t x < 0 := lt_of_not_ge hneg'
    have hprodneg : w t x < 0 := by
      exact mul_neg_of_pos_of_neg (Real.exp_pos _) hvneg
    exact not_lt_of_ge (hw_nonneg t ht x) hprodneg
  exact sub_nonneg.mp (by simpa [v] using hvnonneg)









theorem msm110_ch4_scalar_supersolutions
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (alpha : Real)
    (hw_cont : ContinuousOn (fun p : Real × M => u p.1 p.2 - alpha)
      (spacetimeSlab (M := M) T))
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => u s x - alpha) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => u t y - alpha) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - alpha) y) x)
    (hinit : forall x : M, alpha <= u 0 x)
    (hnegative : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      u t x < alpha ->
        0 <= parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - alpha) t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, alpha <= u t x := by
  let w : Real -> M -> Real := fun t x => u t x - alpha
  have hw0 : forall x : M, 0 <= w 0 x := by
    intro x
    exact sub_nonneg.mpr (hinit x)
  have hneg : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht x hwneg
    exact hnegative t ht x (by simpa [w] using hwneg)
  have hw_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
    strict_barrier_nonnegative (I := I) G T hT X w
      (by simpa [w] using hw_cont) hw0
      (by simpa [w] using hw_time)
      (by simpa [w] using hw_mdiff) (by simpa [w] using hw_grad)
      hneg
  intro t ht x
  exact sub_nonneg.mp (by simpa [w] using hw_nonneg t ht x)





theorem msm110_ch4_scalar_pointwise_bounds
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (C1 C2 : Real) (_hC : C1 <= C2)
    (hlower_cont : ContinuousOn (fun p : Real × M => u p.1 p.2 - C1)
      (spacetimeSlab (M := M) T))
    (hlower_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => u s x - C1) (Set.Icc 0 T) t)
    (hlower_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => u t y - C1) x)
    (hlower_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - C1) y) x)
    (hupper_cont : ContinuousOn (fun p : Real × M => C2 - u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hupper_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => C2 - u s x) (Set.Icc 0 T) t)
    (hupper_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => C2 - u t y) x)
    (hupper_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => C2 - u t z) y) x)
    (hinit_lower : forall x : M, C1 <= u 0 x)
    (hinit_upper : forall x : M, u 0 x <= C2)
    (hlower_negative : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      u t x < C1 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - C1) t x)
    (hupper_negative : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      C2 < u t x ->
        0 <= parabolicOperatorWithDrift (I := I) G T X
          (fun s y => C2 - u s y) t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      C1 <= u t x ∧ u t x <= C2 := by
  have hlower :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, C1 <= u t x :=
    msm110_ch4_scalar_supersolutions (I := I) G T hT X u C1
      hlower_cont hlower_time hlower_mdiff hlower_grad hinit_lower hlower_negative
  have hupper_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= C2 - u t x := by
    simpa using
      (msm110_ch4_scalar_supersolutions (I := I) G T hT X
        (fun t x => C2 - u t x) 0
        (by simpa using hupper_cont)
        (by simpa using hupper_time)
        (by simpa using hupper_mdiff)
        (by simpa using hupper_grad)
        (fun x => sub_nonneg.mpr (hinit_upper x))
        (fun t ht x hneg => by
          simpa using hupper_negative t ht x (by linarith)))
  intro t ht x
  exact ⟨hlower t ht x, sub_nonneg.mp (hupper_nonneg t ht x)⟩






theorem msm110_ch4_scalar_linear_reaction
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (beta : Real -> M -> Real) (C : Real)
    (_hbeta_bound : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      beta t x <= C)
    (hJ_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-C * p.1) * u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hJ_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => Real.exp (-C * s) * u s x) (Set.Icc 0 T) t)
    (hJ_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-C * t) * u t y) x)
    (hJ_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-C * t) * u t z) y) x)
    (hinit : forall x : M, 0 <= u 0 x)
    (hJ_negative : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      Real.exp (-C * t) * u t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X
          (fun s y => Real.exp (-C * s) * u s y) t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= u t x := by
  let J : Real -> M -> Real := fun t x => Real.exp (-C * t) * u t x
  have hJ_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= J t x := by
    simpa [J] using
      (msm110_ch4_scalar_supersolutions (I := I) G T hT X J 0
        (by simpa [J] using hJ_cont)
        (by simpa [J] using hJ_time)
        (by simpa [J] using hJ_mdiff)
        (by simpa [J] using hJ_grad)
        (fun x => by simpa [J] using hinit x)
        (by simpa [J] using hJ_negative))
  intro t ht x
  have hprod : 0 <= Real.exp (-C * t) * u t x := by
    simpa [J] using hJ_nonneg t ht x
  exact (mul_nonneg_iff_of_pos_left (Real.exp_pos (-C * t))).mp hprod






theorem linear_react_nonneg
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (beta : Real -> M -> Real) (C : Real)
    (hbeta : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      beta t x <= C)
    (hJ_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-C * p.1) * u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hJ_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => Real.exp (-C * s) * u s x) (Set.Icc 0 T) t)
    (hJ_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-C * t) * u t y) x)
    (hJ_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-C * t) * u t z) y) x)
    (hu_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hu_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hu_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hreaction : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X u t x =
        beta t x * u t x)
    (hinit : forall x : M, 0 <= u 0 x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= u t x := by
  refine msm110_ch4_scalar_linear_reaction (I := I) G T hT X u beta C hbeta
    hJ_cont hJ_time hJ_mdiff hJ_grad hinit ?_
  intro t ht x hJneg
  by_cases hTpos : 0 < T
  · have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
      uniqueDiffOn_Icc hTpos t ht
    have hscale :
        DifferentiableWithinAt Real (fun s : Real => Real.exp (-C * s))
          (Set.Icc 0 T) t := by
      have hlinear :
          DifferentiableWithinAt Real (fun s : Real => -C * s)
            (Set.Icc 0 T) t := by
        simpa using
          (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul (-C)
      exact hlinear.exp
    rw [parabolic_exp_rescale_identity (I := I) G T C X u t ht huniq
      (hu_space t ht) x (hu_grad t ht x) (hu_time t ht x) hscale]
    rw [hreaction t ht x]
    have hu_neg : u t x < 0 :=
      lt_of_mul_lt_mul_left (by simpa using hJneg) (Real.exp_pos (-C * t)).le
    apply mul_nonneg (Real.exp_pos (-C * t)).le
    calc
      beta t x * u t x - C * u t x = (beta t x - C) * u t x := by ring
      _ >= 0 := mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (hbeta t ht x)) hu_neg.le
  · have hT0 : T = 0 := le_antisymm (le_of_not_gt hTpos) hT
    have ht0 : t = 0 := by
      apply le_antisymm
      · simpa [hT0] using ht.2
      · exact ht.1
    have hu_neg : u 0 x < 0 := by
      rw [ht0] at hJneg
      exact lt_of_mul_lt_mul_left (by simpa using hJneg)
        (Real.exp_pos (-C * 0)).le
    exact False.elim (not_lt_of_ge (hinit x) hu_neg)










theorem scalar_weak_maximum_principle_supersolutions_of_weighted_lipschitz_on_values
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c ρ A : Real -> Real)
    (F : Real -> Real -> Real)
    (hρ_pos : forall t : Real, t ∈ Set.Icc 0 T -> 0 < ρ t)
    (hw_cont : ContinuousOn
      (fun p : Real × M => ρ p.1 * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => ρ s * (u s x - c s)) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => ρ t * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => ρ t * (u t z - c t)) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hlip : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      |F (u t x) t - F (c t) t| <= A t * |u t x - c t|)
    (hsubCalc : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - c s) t x =
        parabolicOperatorWithDrift (I := I) G T X u t x -
          derivWithin c (Set.Icc 0 T) t)
    (hweightCalc : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      parabolicOperatorWithDrift (I := I) G T X
          (fun s y => ρ s * (u s y - c s)) t x =
        ρ t *
          (parabolicOperatorWithDrift (I := I) G T X
              (fun s y => u s y - c s) t x - A t * (u t x - c t))) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  let v : Real -> M -> Real := fun t x => u t x - c t
  let w : Real -> M -> Real := fun t x => ρ t * v t x
  have hw0 : forall x : M, 0 <= w 0 x := by
    intro x
    have h0mem : (0 : Real) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
    have hv0 : 0 <= v 0 x := by
      exact sub_nonneg.mpr (hinit x)
    exact mul_nonneg (le_of_lt (hρ_pos 0 h0mem)) hv0
  have hnegative : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, w t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht x hwneg
    have hρt : 0 < ρ t := hρ_pos t ht
    have hvneg : v t x < 0 := by
      by_contra hnonneg
      have hvnonneg : 0 <= v t x := le_of_not_gt hnonneg
      have hprod : 0 <= ρ t * v t x :=
        mul_nonneg (le_of_lt hρt) hvnonneg
      exact not_le_of_gt (by simpa [w] using hwneg) hprod
    have hPvLower :
        A t * (u t x - c t) <=
          parabolicOperatorWithDrift (I := I) G T X v t x := by
      have hlow : A t * (u t x - c t) <= F (u t x) t - F (c t) t :=
        reaction_difference_lower_bound_on_negative_region
          (hlip t ht x) (by simpa [v] using hvneg)
      have hupper :
          F (u t x) t - F (c t) t <=
            parabolicOperatorWithDrift (I := I) G T X v t x := by
        calc
          F (u t x) t - F (c t) t <=
              parabolicOperatorWithDrift (I := I) G T X u t x -
                derivWithin c (Set.Icc 0 T) t := by
            rw [hode t ht]
            exact sub_le_sub_right (hsuper t ht x) (F (c t) t)
          _ = parabolicOperatorWithDrift (I := I) G T X v t x := by
            have hsub :
                parabolicOperatorWithDrift (I := I) G T X v t x =
                  parabolicOperatorWithDrift (I := I) G T X u t x -
                    derivWithin c (Set.Icc 0 T) t := by
              simpa [v] using hsubCalc t ht x
            exact hsub.symm
      exact le_trans hlow hupper
    have hregion :
        0 <= parabolicOperatorWithDrift (I := I) G T X v t x - A t * v t x := by
      exact sub_nonneg.mpr (by simpa [v] using hPvLower)
    calc
      0 <= ρ t *
          (parabolicOperatorWithDrift (I := I) G T X v t x - A t * v t x) := by
        exact mul_nonneg (le_of_lt hρt) hregion
      _ = parabolicOperatorWithDrift (I := I) G T X w t x := by
        rw [← hweightCalc t ht x]
  have hw_nonneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= w t x :=
    strict_barrier_nonnegative (I := I) G T hT X w
      (by simpa [w, v] using hw_cont) hw0
      (by simpa [w, v] using hw_time)
      (by simpa [w, v] using hw_mdiff) (by simpa [w, v] using hw_grad)
      hnegative
  intro t ht x
  have hvnonneg : 0 <= v t x := by
    by_contra hneg'
    have hvneg : v t x < 0 := lt_of_not_ge hneg'
    have hprodneg : w t x < 0 := by
      exact mul_neg_of_pos_of_neg (hρ_pos t ht) hvneg
    exact not_lt_of_ge (hw_nonneg t ht x) hprodneg
  exact sub_nonneg.mp (by simpa [v] using hvnonneg)








theorem scalar_wmp_supersolutions_of_lipschitz_on_values_of_regular
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (L : Real)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-L * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-L * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-L * t) * (u t z - c t)) y) x)
    (hu_time : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hu_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => u t z - c t) y)
    (hv_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - c t) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hlip : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      |F (u t x) t - F (c t) t| <= L * |u t x - c t|) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  by_cases hTpos : 0 < T
  · refine scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_values
      (I := I) G T hT X u c F L hw_cont ?_ hw_mdiff hw_grad
      hsuper hode hinit hlip ?_ ?_
    · intro t ht x
      have hv_time :
          DifferentiableWithinAt Real (fun s : Real => u s x - c s)
            (Set.Icc 0 T) t :=
        (hu_time t ht x).sub (hc_time t ht)
      have hscale :
          DifferentiableWithinAt Real (fun s : Real => Real.exp (-L * s))
            (Set.Icc 0 T) t := by
        have hlinear :
            DifferentiableWithinAt Real (fun s : Real => -L * s) (Set.Icc 0 T) t := by
          simpa using
            (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul (-L)
        exact hlinear.exp
      exact hscale.mul hv_time
    · intro t ht x
      exact parabolic_sub_time_curve_identity (I := I) G T X u c t ht
        (hu_space t ht) x (hu_time t ht x) (hc_time t ht)
    · intro t ht x
      have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
        uniqueDiffOn_Icc hTpos t ht
      have hv_time :
          DifferentiableWithinAt Real (fun s : Real => u s x - c s)
            (Set.Icc 0 T) t :=
        (hu_time t ht x).sub (hc_time t ht)
      have hscale :
          DifferentiableWithinAt Real (fun s : Real => Real.exp (-L * s))
            (Set.Icc 0 T) t := by
        have hlinear :
            DifferentiableWithinAt Real (fun s : Real => -L * s) (Set.Icc 0 T) t := by
          simpa using
            (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul (-L)
        exact hlinear.exp
      exact parabolic_exp_rescale_identity (I := I) G T L X
        (fun s y => u s y - c s) t ht huniq (hv_space t ht) x
        (hv_grad t ht x) hv_time hscale
  · have hTle : T <= 0 := le_of_not_gt hTpos
    have hT0 : T = 0 := le_antisymm hTle hT
    intro t ht x
    have ht0 : t = 0 := by
      have htle : t <= 0 := by
        simpa [hT0] using ht.2
      exact le_antisymm htle ht.1
    simpa [ht0] using hinit x



theorem scalar_wmp_supersolutions_of_lipschitz_on_values_of_regular_positive_time
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (L : Real)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-L * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-L * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-L * t) * (u t z - c t)) y) x)
    (hu_time : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hu_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => u t z - c t) y)
    (hv_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - c t) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hlip : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      |F (u t x) t - F (c t) t| <= L * |u t x - c t|) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  by_cases hTpos : 0 < T
  · refine scalar_weak_maximum_principle_supersolutions_of_lipschitz_on_values_of_positive_time
      (I := I) G T hT X u c F L hw_cont ?_ hw_mdiff hw_grad
      hsuper hode hinit hlip ?_ ?_
    · intro t ht x
      have hv_time :
          DifferentiableWithinAt Real (fun s : Real => u s x - c s)
            (Set.Icc 0 T) t :=
        (hu_time t ht x).sub (hc_time t ht)
      have hscale :
          DifferentiableWithinAt Real (fun s : Real => Real.exp (-L * s))
            (Set.Icc 0 T) t := by
        have hlinear :
            DifferentiableWithinAt Real (fun s : Real => -L * s) (Set.Icc 0 T) t := by
          simpa using
            (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul (-L)
        exact hlinear.exp
      exact hscale.mul hv_time
    · intro t ht x
      exact parabolic_sub_time_curve_identity (I := I) G T X u c t ht
        (hu_space t ht) x (hu_time t ht x) (hc_time t ht)
    · intro t ht x
      have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
        uniqueDiffOn_Icc hTpos t ht
      have hv_time :
          DifferentiableWithinAt Real (fun s : Real => u s x - c s)
            (Set.Icc 0 T) t :=
        (hu_time t ht x).sub (hc_time t ht)
      have hscale :
          DifferentiableWithinAt Real (fun s : Real => Real.exp (-L * s))
            (Set.Icc 0 T) t := by
        have hlinear :
            DifferentiableWithinAt Real (fun s : Real => -L * s) (Set.Icc 0 T) t := by
          simpa using
            (differentiableWithinAt_id' (𝕜 := Real) (s := Set.Icc 0 T) (x := t)).const_mul (-L)
        exact hlinear.exp
      exact parabolic_exp_rescale_identity (I := I) G T L X
        (fun s y => u s y - c s) t ht huniq (hv_space t ht) x
        (hv_grad t ht x) hv_time hscale
  · have hTle : T <= 0 := le_of_not_gt hTpos
    have hT0 : T = 0 := le_antisymm hTle hT
    intro t ht x
    have ht0 : t = 0 := by
      have htle : t <= 0 := by
        simpa [hT0] using ht.2
      exact le_antisymm htle ht.1
    simpa [ht0] using hinit x




def scalarValueSet (u : Real -> M -> Real) (c : Real -> Real) (t : Real) : Set Real :=
  Set.range (fun x : M => u t x) ∪ {c t}


theorem scalarValueSet_isCompact_of_continuous
    [CompactSpace M]
    (u : Real -> M -> Real) (c : Real -> Real) (t : Real)
    (hu : Continuous (fun x : M => u t x)) :
    IsCompact (scalarValueSet (M := M) u c t) := by
  have hrange : IsCompact (Set.range (fun x : M => u t x)) := by
    simpa using (isCompact_univ.image hu)
  exact hrange.union isCompact_singleton



theorem exists_abs_lipschitzOnWith_of_locallyLipschitzOn_isCompact
    {f : Real -> Real} {s : Set Real}
    (hs : IsCompact s)
    (hf : LocallyLipschitzOn s f) :
    ∃ K : NNReal, ∀ a ∈ s, ∀ b ∈ s,
      |f a - f b| <= (K : Real) * |a - b| := by
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs hf
  refine ⟨K, ?_⟩
  intro a ha b hb
  simpa [Real.dist_eq] using hK.dist_le_mul a ha b hb



omit [TopologicalSpace M] in
theorem exists_time_dependent_lipschitz_bound_on_values
    (F : Real -> Real -> Real)
    (u : Real -> M -> Real) (c : Real -> Real) (T : Real)
    (hF : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LocallyLipschitzOn (scalarValueSet (M := M) u c t)
        (fun a : Real => F a t))
    (hcompact : ∀ t : Real, t ∈ Set.Icc 0 T ->
      IsCompact (scalarValueSet (M := M) u c t)) :
    ∃ A : Real -> Real,
      (∀ t : Real, t ∈ Set.Icc 0 T -> 0 <= A t) ∧
      (∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
        |F (u t x) t - F (c t) t| <= A t * |u t x - c t|) := by
  classical
  have hExists : ∀ t : Real, t ∈ Set.Icc 0 T ->
      ∃ K : NNReal, ∀ a ∈ scalarValueSet (M := M) u c t,
        ∀ b ∈ scalarValueSet (M := M) u c t,
          |(fun a : Real => F a t) a - (fun a : Real => F a t) b| <=
            (K : Real) * |a - b| := by
    intro t ht
    exact exists_abs_lipschitzOnWith_of_locallyLipschitzOn_isCompact
      (hcompact t ht) (hF t ht)
  let A : Real -> Real := fun t =>
    if ht : t ∈ Set.Icc 0 T then
      ((Classical.choose (hExists t ht) : NNReal) : Real)
    else
      0
  refine ⟨A, ?_, ?_⟩
  · intro t ht
    dsimp [A]
    rw [dif_pos ht]
    exact NNReal.coe_nonneg _
  · intro t ht x
    dsimp [A]
    rw [dif_pos ht]
    have hu_mem : u t x ∈ scalarValueSet (M := M) u c t := by
      left
      exact ⟨x, rfl⟩
    have hc_mem : c t ∈ scalarValueSet (M := M) u c t := by
      right
      rfl
    exact Classical.choose_spec (hExists t ht) (u t x) hu_mem (c t) hc_mem


omit [TopologicalSpace M] in
theorem exists_time_dependent_lipschitz_bound_on_values_of_locallyLipschitz
    (F : Real -> Real -> Real)
    (u : Real -> M -> Real) (c : Real -> Real) (T : Real)
    (hF : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LocallyLipschitz (fun a : Real => F a t))
    (hcompact : ∀ t : Real, t ∈ Set.Icc 0 T ->
      IsCompact (scalarValueSet (M := M) u c t)) :
    ∃ A : Real -> Real,
      (∀ t : Real, t ∈ Set.Icc 0 T -> 0 <= A t) ∧
      (∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
        |F (u t x) t - F (c t) t| <= A t * |u t x - c t|) := by
  exact exists_time_dependent_lipschitz_bound_on_values (M := M) F u c T
    (fun t ht => (hF t ht).locallyLipschitzOn) hcompact


def scalarWMPValueSet (T : Real) (u : Real -> M -> Real) (c : Real -> Real) : Set Real :=
  (fun p : Real × M => u p.1 p.2) '' spacetimeSlab (M := M) T ∪ c '' Set.Icc 0 T


omit [TopologicalSpace M] in
theorem scalarWMPValueSet_u_mem
    (T : Real) (u : Real -> M -> Real) (c : Real -> Real)
    {t : Real} (ht : t ∈ Set.Icc 0 T) (x : M) :
    u t x ∈ scalarWMPValueSet (M := M) T u c := by
  left
  refine ⟨(t, x), ?_, rfl⟩
  exact ⟨ht, trivial⟩


omit [TopologicalSpace M] in
theorem scalarWMPValueSet_c_mem
    (T : Real) (u : Real -> M -> Real) (c : Real -> Real)
    {t : Real} (ht : t ∈ Set.Icc 0 T) :
    c t ∈ scalarWMPValueSet (M := M) T u c := by
  right
  exact ⟨t, ht, rfl⟩



theorem scalarWMPValueSet_isCompact
    [CompactSpace M]
    (T : Real) (u : Real -> M -> Real) (c : Real -> Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hc_cont : ContinuousOn c (Set.Icc 0 T)) :
    IsCompact (scalarWMPValueSet (M := M) T u c) := by
  have hslab : IsCompact (spacetimeSlab (M := M) T) := by
    simpa [spacetimeSlab] using (isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set M)))
  exact (hslab.image_of_continuousOn hu_cont).union (isCompact_Icc.image_of_continuousOn hc_cont)



omit [TopologicalSpace M] in
theorem scalarWMP_lipschitz_on_valueSet_bound
    (T : Real) (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (K : NNReal)
    (hF_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => F a t)
        (scalarWMPValueSet (M := M) T u c)) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      |F (u t x) t - F (c t) t| <= (K : Real) * |u t x - c t| := by
  intro t ht x
  have hu_mem : u t x ∈ scalarWMPValueSet (M := M) T u c :=
    scalarWMPValueSet_u_mem (M := M) T u c ht x
  have hc_mem : c t ∈ scalarWMPValueSet (M := M) T u c :=
    scalarWMPValueSet_c_mem (M := M) T u c ht
  simpa [Real.dist_eq] using (hF_lip t ht).dist_le_mul (u t x) hu_mem (c t) hc_mem








theorem scalar_wmp_supersolutions_of_lipschitz_on_value_set_of_regular
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (K : NNReal)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-(K : Real) * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-(K : Real) * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-(K : Real) * t) * (u t z - c t)) y) x)
    (hu_time : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hu_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => u t z - c t) y)
    (hv_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - c t) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hF_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => F a t)
        (scalarWMPValueSet (M := M) T u c)) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  exact scalar_wmp_supersolutions_of_lipschitz_on_values_of_regular
    (I := I) G T hT X u c F (K : Real)
    hw_cont hw_mdiff hw_grad hu_time hc_time hu_space hv_space hv_grad
    hsuper hode hinit
    (scalarWMP_lipschitz_on_valueSet_bound (M := M) T u c F K hF_lip)



theorem scalar_wmp_supersolutions_of_lipschitz_on_value_set_of_regular_positive_time
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (K : NNReal)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-(K : Real) * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-(K : Real) * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-(K : Real) * t) * (u t z - c t)) y) x)
    (hu_time : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hu_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => u t z - c t) y)
    (hv_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - c t) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> 0 < t -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hF_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => F a t)
        (scalarWMPValueSet (M := M) T u c)) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  exact scalar_wmp_supersolutions_of_lipschitz_on_values_of_regular_positive_time
    (I := I) G T hT X u c F (K : Real)
    hw_cont hw_mdiff hw_grad hu_time hc_time hu_space hv_space hv_grad
    hsuper hode hinit
    (scalarWMP_lipschitz_on_valueSet_bound (M := M) T u c F K hF_lip)








theorem scalar_wmp_super_theorem_7_1
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (K : NNReal)
    (_hF_mono : forall t : Real, t ∈ Set.Icc 0 T -> Monotone (fun a : Real => F a t))
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-(K : Real) * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-(K : Real) * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-(K : Real) * t) * (u t z - c t)) y) x)
    (hu_time : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hu_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => u t z - c t) y)
    (hv_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - c t) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) t <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t) t)
    (hinit : forall x : M, c 0 <= u 0 x)
    (hF_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => F a t)
        (scalarWMPValueSet (M := M) T u c)) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x :=
  scalar_wmp_supersolutions_of_lipschitz_on_value_set_of_regular
    (I := I) G T hT X u c F K hw_cont hw_mdiff hw_grad hu_time hc_time
    hu_space hv_space hv_grad hsuper hode hinit hF_lip








theorem scalar_wmp_sub_theorem_7_2
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real -> Real) (K : NNReal)
    (hF_mono : forall t : Real, t ∈ Set.Icc 0 T -> Monotone (fun a : Real => F a t))
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-(K : Real) * p.1) *
        ((-u p.1 p.2) - (-c p.1)))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-(K : Real) * t) *
          ((-u t y) - (-c t))) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-(K : Real) * t) *
            ((-u t z) - (-c t))) y) x)
    (hneg_u_time : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => -u s x) (Set.Icc 0 T) t)
    (hneg_c_time : forall t : Real, t ∈ Set.Icc 0 T ->
      DifferentiableWithinAt Real (fun s : Real => -c s) (Set.Icc 0 T) t)
    (hneg_u_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => -u t z) y)
    (hneg_v_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => (-u t z) - (-c t)) y)
    (hneg_v_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => (-u t z) - (-c t)) y) x)
    (hsub_as_super : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      (fun a : Real => -F (-a) t) (-u t x) <=
        parabolicOperatorWithDrift (I := I) G T X
          (fun s y => -u s y) t x)
    (hode_neg : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin (fun s : Real => -c s) (Set.Icc 0 T) t =
        (fun a : Real => -F (-a) t) (-c t))
    (hinit : forall x : M, u 0 x <= c 0)
    (hF_lip_neg : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => -F (-a) t)
        (scalarWMPValueSet (M := M) T
          (fun t x => -u t x) (fun t => -c t))) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, u t x <= c t := by
  have hG_mono : forall t : Real, t ∈ Set.Icc 0 T ->
      Monotone (fun a : Real => -F (-a) t) := by
    intro t ht a b hab
    exact neg_le_neg (hF_mono t ht (neg_le_neg hab))
  have hneg :
      forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, -c t <= -u t x :=
    scalar_wmp_super_theorem_7_1
      (I := I) G T hT X (fun t x => -u t x) (fun t => -c t)
      (fun a t => -F (-a) t) K hG_mono
      hw_cont hw_mdiff hw_grad hneg_u_time hneg_c_time
      hneg_u_space hneg_v_space hneg_v_grad hsub_as_super hode_neg
      (fun x => by linarith [hinit x]) hF_lip_neg
  intro t ht x
  linarith [hneg t ht x]







theorem msm110_ch4_scalar_ode_lower
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real) (K : NNReal) (_hF_mono : Monotone F)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-(K : Real) * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-(K : Real) * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-(K : Real) * t) * (u t z - c t)) y) x)
    (hu_time : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hu_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => u t z - c t) y)
    (hv_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - c t) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t))
    (hinit : forall x : M, c 0 <= u 0 x)
    (hF_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => F a)
        (scalarWMPValueSet (M := M) T u c)) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  refine scalar_wmp_supersolutions_of_lipschitz_on_value_set_of_regular
    (I := I) G T hT X u c (fun a _ => F a) K
    hw_cont hw_mdiff hw_grad hu_time hc_time hu_space hv_space hv_grad
    ?_ ?_ hinit ?_
  · intro t ht x
    exact hsuper t ht x
  · intro t ht
    exact hode t ht
  · intro t ht
    simpa using hF_lip t ht

end

end DifferentialGeometry.Integral.Connection
