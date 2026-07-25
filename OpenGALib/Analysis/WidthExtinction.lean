import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The width inequality forces extinction

A nonnegative continuous quantity `W` whose forward Dini derivative
satisfies
$$\frac{d}{dt} W(t) \;\le\; -4\pi + \frac{3}{4(t+C)}\, W(t)$$
cannot live past the explicit deadline
$$T^* \;=\; \Big(C^{1/4} + \frac{W(0)}{16\pi\, C^{3/4}}\Big)^{4} - C .$$

This is the pure-calculus endpoint of the Colding–Minicozzi finite-time
extinction argument: the width of a nontrivial sweepout class along a
Ricci flow satisfies the displayed inequality, is nonnegative by
definition, and therefore the flow cannot be immortal. All geometry is
upstream, in the two constants; this file is analysis only.

The differential inequality enters in the weakest useful sense — the
liminf of forward difference quotients (`slope`), the form consumed by
Mathlib's fencing lemmas. It is implied both by the limsup-of-forward-
difference-quotients hypothesis of the blueprint and by any pointwise
right-differentiable version, so every downstream supplier can
instantiate it.

## Ground truth

Colding–Minicozzi, *Estimates for the extinction time for the Ricci
flow on certain 3-manifolds and a question of Perelman*, §1 (the
integration displayed between Theorem 0.1 and its corollary).
Blueprint: PoincareNet card `lem-width-inequality-forces-extinction`
(id `aa4c3210ae78`).

## Main declarations

* `widthExtinctionTime C W₀` — the explicit deadline `T*(C, W₀)`.
* `le_widthExtinctionTime_of_slope_le` — a nonnegative continuous `W`
  satisfying the width differential inequality on `[0, t]` forces
  `t ≤ widthExtinctionTime C (W 0)`.

## Proof shape

No integrating factor is applied to `W` itself (transporting Dini
bounds through a product costs an epsilon-management detour). Instead,
for each `ε > 0` the *explicit* solution of the perturbed comparison
equation `B' = 3/(4(t+C))·B - 4π + ε`, `B 0 = W 0 + ε`, is written
down in closed form and Mathlib's contact fencing lemma
`image_le_of_liminf_slope_right_lt_deriv_boundary'` pins `W ≤ B`:
at a contact point `W x = B x` the hypothesised Dini bound for `W` is
*strictly* below `B'`. Letting `ε ↓ 0` and reading the sign of the
limit solution at `t` yields the deadline.
-/

open Set Topology
open scoped Topology

namespace OpenGA

/-- **Math.** The **extinction deadline** $T^*(C, W_0) = \big(C^{1/4} +
\frac{W_0}{16\pi C^{3/4}}\big)^4 - C$: past this time, no nonnegative
quantity can satisfy the width differential inequality. -/
noncomputable def widthExtinctionTime (C W₀ : ℝ) : ℝ :=
  (C ^ ((1 : ℝ)/4) + W₀ / (16 * Real.pi * C ^ ((3 : ℝ)/4))) ^ (4 : ℕ) - C

namespace WidthExtinction

/-- **Eng.** Right derivative of the shifted power `y ↦ (y + C) ^ p`,
valid wherever `0 < x + C`. -/
private lemma hasDerivWithinAt_shift_rpow (C p : ℝ) {x : ℝ} (hx : 0 < x + C)
    (s : Set ℝ) :
    HasDerivWithinAt (fun y : ℝ => (y + C) ^ p) (p * (x + C) ^ (p - 1)) s x := by
  have h := ((hasDerivAt_id x).add_const C).rpow_const (p := p) (Or.inl hx.ne')
  simpa using h.hasDerivWithinAt

/-- **Math.** The explicit solution of the perturbed comparison equation
$B' = \frac{3}{4(t+C)} B - 4\pi + \varepsilon$ with $B(0) = W_0 +
\varepsilon$. -/
private noncomputable def comparison (C W₀ ε x : ℝ) : ℝ :=
  (W₀ + ε) / C ^ ((3 : ℝ)/4) * (x + C) ^ ((3 : ℝ)/4)
    + 4 * (ε - 4 * Real.pi)
      * ((x + C) - C ^ ((1 : ℝ)/4) * (x + C) ^ ((3 : ℝ)/4))

/-- **Eng.** The literal derivative expression of `comparison`. -/
private noncomputable def comparisonDeriv (C W₀ ε x : ℝ) : ℝ :=
  (W₀ + ε) / C ^ ((3 : ℝ)/4) * ((3 : ℝ)/4 * (x + C) ^ ((3 : ℝ)/4 - 1))
    + 4 * (ε - 4 * Real.pi)
      * (1 - C ^ ((1 : ℝ)/4) * ((3 : ℝ)/4 * (x + C) ^ ((3 : ℝ)/4 - 1)))

private lemma comparison_hasDerivWithinAt (C W₀ ε : ℝ) {x : ℝ}
    (hx : 0 < x + C) (s : Set ℝ) :
    HasDerivWithinAt (comparison C W₀ ε) (comparisonDeriv C W₀ ε x) s x := by
  have h1 := hasDerivWithinAt_shift_rpow C ((3 : ℝ)/4) hx s
  have h2 : HasDerivWithinAt (fun y : ℝ => y + C) 1 s x :=
    ((hasDerivAt_id x).add_const C).hasDerivWithinAt
  exact (h1.const_mul _).add (((h2.sub (h1.const_mul _)).const_mul _))

/-- **Math.** `comparison` solves the perturbed comparison equation. -/
private lemma comparisonDeriv_eq (C W₀ ε : ℝ) {x : ℝ} (hC : 0 < C)
    (hx : 0 < x + C) :
    comparisonDeriv C W₀ ε x
      = 3 / (4 * (x + C)) * comparison C W₀ ε x + (ε - 4 * Real.pi) := by
  have hC34 : C ^ ((3 : ℝ)/4) ≠ 0 := by positivity
  have hpow : (x + C) ^ ((3 : ℝ)/4 - 1) = (x + C) ^ ((3 : ℝ)/4) / (x + C) := by
    rw [Real.rpow_sub hx, Real.rpow_one]
  unfold comparison comparisonDeriv
  rw [hpow]
  field_simp
  ring

/-- **Math.** Initial value: `comparison C W₀ ε 0 = W₀ + ε`. -/
private lemma comparison_zero (W₀ ε : ℝ) {C : ℝ} (hC : 0 < C) :
    comparison C W₀ ε 0 = W₀ + ε := by
  have h1 : C ^ ((1 : ℝ)/4) * C ^ ((3 : ℝ)/4) = C := by
    rw [← Real.rpow_add hC]
    norm_num
  have h2 : (W₀ + ε) / C ^ ((3 : ℝ)/4) * C ^ ((3 : ℝ)/4) = W₀ + ε :=
    div_mul_cancel₀ _ (by positivity)
  unfold comparison
  rw [zero_add, h1, h2]
  ring

private lemma comparison_continuousOn (C W₀ ε : ℝ) {t : ℝ} :
    ContinuousOn (comparison C W₀ ε) (Icc 0 t) := by
  have hbase : ContinuousOn (fun x : ℝ => x + C) (Icc 0 t) :=
    (continuous_id.add continuous_const).continuousOn
  have hf : ContinuousOn (fun x : ℝ => (x + C) ^ ((3 : ℝ)/4)) (Icc 0 t) :=
    hbase.rpow_const fun x _ => Or.inr (by norm_num)
  exact (continuousOn_const.mul hf).add
    (continuousOn_const.mul (hbase.sub (continuousOn_const.mul hf)))

end WidthExtinction

open WidthExtinction in
/-- **Math.** **The width inequality forces extinction** (Colding–
Minicozzi; PoincareNet card `lem-width-inequality-forces-extinction`).

Let `W` be continuous on `[0, t]` and nonnegative at the right end
(nonnegativity is needed nowhere else), and suppose that at every
`x ∈ [0, t)` the liminf of forward difference quotients of `W` is
bounded by
$$-4\pi + \frac{3}{4(x+C)}\, W(x)$$
(the hypothesis `hslope`, in Mathlib's frequently-`slope` phrasing).
Then `t` cannot exceed the explicit deadline
`widthExtinctionTime C (W 0)`.

Downstream, `W` is the sweepout width of a Ricci flow (with surgery),
`hslope` is supplied by the width evolution inequality, and the
conclusion bounds the extinction time of the flow. -/
theorem le_widthExtinctionTime_of_slope_le
    {C t : ℝ} {W : ℝ → ℝ} (hC : 0 < C) (ht : 0 ≤ t)
    (hWt : 0 ≤ W t)
    (hcont : ContinuousOn W (Icc 0 t))
    (hslope : ∀ x ∈ Ico 0 t, ∀ r,
      -(4 * Real.pi) + 3 / (4 * (x + C)) * W x < r →
        ∃ᶠ z in 𝓝[>] x, slope W x z < r) :
    t ≤ widthExtinctionTime C (W 0) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have htC : 0 < t + C := by linarith
  -- Step 1: fencing against the perturbed explicit solution, for every ε > 0.
  have key : ∀ ε > (0 : ℝ), W t ≤ comparison C (W 0) ε t := by
    intro ε hε
    refine image_le_of_liminf_slope_right_lt_deriv_boundary'
      (f := W) (f' := fun x => -(4 * Real.pi) + 3 / (4 * (x + C)) * W x)
      (B := comparison C (W 0) ε) (B' := fun x => comparisonDeriv C (W 0) ε x)
      hcont hslope ?_ (comparison_continuousOn C (W 0) ε) ?_ ?_
      (right_mem_Icc.2 ht)
    · rw [comparison_zero (W 0) ε hC]
      linarith
    · intro x hx
      have hxC : 0 < x + C := by
        have := hx.1
        linarith
      exact comparison_hasDerivWithinAt C (W 0) ε hxC (Ici x)
    · intro x hx hcontact
      have hxC : 0 < x + C := by
        have := hx.1
        linarith
      rw [comparisonDeriv_eq C (W 0) ε hC hxC, ← hcontact]
      linarith
  -- Step 2: let ε ↓ 0 through the closure of `Ioi 0`.
  have hle : W t ≤ comparison C (W 0) 0 t := by
    have hcε : ContinuousWithinAt (fun ε => comparison C (W 0) ε t) (Ioi 0) 0 := by
      unfold WidthExtinction.comparison
      fun_prop
    have h0 : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by
      rw [closure_Ioi]
      exact Set.self_mem_Ici
    have h := ContinuousWithinAt.closure_le (f := fun _ : ℝ => W t)
      (g := fun ε : ℝ => comparison C (W 0) ε t)
      h0 continuousWithinAt_const hcε key
    simpa using h
  -- Step 3: read off the deadline from the sign of the limit solution.
  set A : ℝ := (t + C) ^ ((1 : ℝ)/4) with hA
  have hApos : 0 < A := Real.rpow_pos_of_pos htC _
  have hA3 : (t + C) ^ ((3 : ℝ)/4) = A ^ (3 : ℕ) := by
    rw [hA, ← Real.rpow_natCast ((t + C) ^ ((1 : ℝ)/4)) 3,
      ← Real.rpow_mul htC.le]
    norm_num
  have hA4 : t + C = A ^ (4 : ℕ) := by
    rw [hA, ← Real.rpow_natCast ((t + C) ^ ((1 : ℝ)/4)) 4,
      ← Real.rpow_mul htC.le]
    norm_num
  -- 0 ≤ comparison at t, with the ε = 0 solution factored through A.
  have hsign : 0 ≤ W 0 / C ^ ((3 : ℝ)/4) - 16 * Real.pi * (A - C ^ ((1 : ℝ)/4)) := by
    have h0B : 0 ≤ comparison C (W 0) 0 t := hWt.trans hle
    have hfactor : comparison C (W 0) 0 t
        = A ^ (3 : ℕ)
          * (W 0 / C ^ ((3 : ℝ)/4) - 16 * Real.pi * (A - C ^ ((1 : ℝ)/4))) := by
      unfold WidthExtinction.comparison
      rw [hA3, hA4]
      ring
    rw [hfactor] at h0B
    have hA3pos : (0 : ℝ) < A ^ (3 : ℕ) := by positivity
    exact nonneg_of_mul_nonneg_right h0B hA3pos
  -- Solve for A, then raise to the fourth power.
  have hAle : A ≤ C ^ ((1 : ℝ)/4) + W 0 / (16 * Real.pi * C ^ ((3 : ℝ)/4)) := by
    have h16π : (0 : ℝ) < 16 * Real.pi := by positivity
    have hdiv : W 0 / C ^ ((3 : ℝ)/4) / (16 * Real.pi)
        = W 0 / (16 * Real.pi * C ^ ((3 : ℝ)/4)) := by
      rw [div_div, mul_comm]
    have hstep : A - C ^ ((1 : ℝ)/4) ≤ W 0 / C ^ ((3 : ℝ)/4) / (16 * Real.pi) := by
      rw [le_div_iff₀ h16π]
      linarith [hsign]
    rw [← hdiv]
    linarith [hstep]
  have hpow : A ^ (4 : ℕ)
      ≤ (C ^ ((1 : ℝ)/4) + W 0 / (16 * Real.pi * C ^ ((3 : ℝ)/4))) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hApos.le hAle 4
  rw [← hA4] at hpow
  unfold widthExtinctionTime
  linarith

end OpenGA
