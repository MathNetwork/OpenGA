import AltRegularity.Sweepout.ONVP
import AltRegularity.GMT.Varifold

/-!
# AltRegularity.Sweepout.MinMaxLimit

Min-max varifold convergence at a critical parameter, the convergence
predicates packaged from a min-max sequence (used by the DLT criterion),
and the Case 1 fact about points outside the closure of the limit slice.

Encodes the conclusion of the pull-tight argument from Section 3 of the
paper: along a min-max sequence $t_i \to t_0$, the slice boundaries
$|\partial^*\Omega_{t_i}|$ converge to a stationary varifold $V$ with
total mass equal to the width $W(\Phi)$.

The three convergence predicates `SlicesL1Converge`, `DChiWeakConverge`,
and `PerimeterConverge` package the standard ingredients of the
De Lellis–Tasnady integrality criterion (Section 6.1):
  * **L¹ convergence** of slice carriers, automatic from flat-continuity
    of $\Phi$ and a min-max sequence.
  * **Weak measure convergence** of distributional derivatives
    $D\chi_{\Omega(t_i)} \to D\chi_{\Omega(t_0)}$, automatic from L¹
    convergence of indicators.
  * **Perimeter convergence** $\mathrm{Per}(\Omega(t_i)) \to \mathrm{Per}(\Omega(t_0))$,
    which holds **iff** the no-mass-cancellation hypothesis holds.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Sweepout

/-- Min-max convergence at $t_0$: there is a sequence $t_i \nearrow t_0$
along which $|\partial^*\Omega_{t_i}| \to V$ as varifolds. -/
opaque MinMaxLimit : Sweepout M → ℝ → Varifold M → Prop

/-! ## Convergence predicates packaged from a min-max sequence -/

/-- $L^1$ convergence of slice carriers along the min-max sequence
$t_i \to t_0$: $\mathrm{Vol}(\Omega(t_i) \,\triangle\, \Omega(t_0)) \to 0$. -/
opaque SlicesL1Converge : Sweepout M → ℝ → Prop

/-- Weak convergence of the distributional derivatives of the indicator
functions: $D\chi_{\Omega(t_i)} \to D\chi_{\Omega(t_0)}$ in the sense of
measures along the min-max sequence. -/
opaque DChiWeakConverge : Sweepout M → ℝ → Prop

/-- Perimeter convergence along the min-max sequence:
$\mathrm{Per}(\Omega(t_i)) \to \mathrm{Per}(\Omega(t_0))$. -/
opaque PerimeterConverge : Sweepout M → ℝ → Prop

/-! ## Structural facts -/

/-- The total varifold mass of a min-max limit equals the width. -/
theorem minmax_mass_eq_width {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (h : MinMaxLimit Φ t₀ V) : Varifold.mass V = width Φ := by sorry

/-- **(a) Flat continuity → L¹ convergence (paper §6.1 line 1).**
A min-max limit's underlying sequence has $L^1$-converging slice carriers,
since $\Phi$ is continuous in the flat topology. -/
theorem l1Convergence_of_minmaxLimit
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hlim : MinMaxLimit Φ t₀ V) : SlicesL1Converge Φ t₀ := by sorry

/-- **(b) L¹ convergence → weak measure convergence (paper §6.1 line 1, second clause).**
$L^1$ convergence of indicators implies weak convergence of the
distributional derivatives. This is a general fact about BV functions. -/
theorem dChiWeak_of_l1
    {Φ : Sweepout M} {t₀ : ℝ}
    (hL1 : SlicesL1Converge Φ t₀) : DChiWeakConverge Φ t₀ := by sorry

/-! ## Case 1 fact (used by `AltRegularity.PositiveDensity`) -/

/-- **Case 1 fact.** If $p$ lies outside the topological closure of the
limit slice $\Omega_{t_0}$, then by ascending nestedness
$\Omega_{t_i} \subset \Omega_{t_0}$ for every $i$ in the min-max sequence,
and Portmanteau on $|\partial^*\Omega_{t_i}| \to V$ gives
$\|V\|(B_\delta(p)) = 0$, so $p \notin \mathrm{spt}\|V\|$. -/
theorem outside_closure_not_in_spt
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M} {p : M}
    (honvp : ONVP Φ) (hlim : MinMaxLimit Φ t₀ V)
    (hout : p ∉ (Φ.slice t₀).topClosure) :
    p ∉ Varifold.support V := by sorry

end Sweepout

end AltRegularity
