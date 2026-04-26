import AltRegularity.Sweepout.ONVP
import AltRegularity.Sweepout.NonExcessive
import AltRegularity.GMT.Varifold

/-!
# AltRegularity.Sweepout.MinMaxLimit

Min-max varifold convergence at a critical parameter (paper Def 3.3,
last paragraph), the convergence predicates packaged from a min-max
sequence (used by the DLT criterion of paper §6.1), and the Case 1
fact about points outside the closure of the limit slice.

## Definition style

`MinMaxLimit` is an explicit `def`: there exists a sequence
$x_i \in [0,1]$ with $x_i \to x_0$ such that the boundary varifolds
$|\partial^*\Omega(x_i)|$ converge weakly to $V$ and $\|V\|(M) = W(\Phi)$.
This is the precise content of paper Def 3.3's "min-max sequence".

Two leaf primitives carry the GMT content not yet in Mathlib:
  * `Varifold.VarifoldConverge` — weak varifold convergence
    $V_i \to V$ as Radon measures on the Grassmann bundle.
  * `Varifold.ofBoundary` — the boundary varifold $|\partial^*\Omega|$
    of a finite-perimeter set.

The three convergence predicates `SlicesL1Converge`, `DChiWeakConverge`,
and `PerimeterConverge` package the standard ingredients of the
De Lellis–Tasnady integrality criterion (paper §6.1):
  * **L¹ convergence** of slice carriers, automatic from flat-continuity
    of $\Phi$ and a min-max sequence.
  * **Weak measure convergence** of distributional derivatives
    $D\chi_{\Omega(t_i)} \to D\chi_{\Omega(t_0)}$, automatic from L¹
    convergence of indicators.
  * **Perimeter convergence** $\mathrm{Per}(\Omega(t_i)) \to
    \mathrm{Per}(\Omega(t_0))$, which holds **iff** the
    no-mass-cancellation hypothesis holds.
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

namespace Sweepout

/-- $V$ is a **min-max varifold limit** of $\Phi$ at the parameter
$x_0$ (paper Def 3.3, last paragraph): there is a sequence
$x_i \in [0,1]$ with $x_i \to x_0$ such that the boundary varifolds
$|\partial^*\Omega(x_i)|$ converge weakly to $V$ and $\|V\|(M) = W(\Phi)$.

Defined explicitly as an existential over the approximating sequence
and the convergence + mass-equality conditions. -/
def MinMaxLimit (Φ : Sweepout M) (x₀ : ℝ) (V : Varifold M) : Prop :=
  ∃ x : ℕ → ℝ,
    (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧
    Filter.Tendsto x Filter.atTop (nhds x₀) ∧
    Varifold.VarifoldConverge (fun i => Varifold.ofBoundary (Φ.slice (x i))) V ∧
    Varifold.mass V = Sweepout.width Φ

/-! ## Convergence predicates packaged from a min-max sequence -/

/-- $L^1$ convergence of slice carriers along the min-max sequence
$t_i \to t_0$: $\mathrm{Vol}(\Omega(t_i) \,\triangle\, \Omega(t_0)) \to 0$.

**Ground truth**: Simon 1983 §13–§14 (BV functions and finite-perimeter
sets, $L^1_{\mathrm{loc}}$ convergence of indicators). -/
opaque SlicesL1Converge : Sweepout M → ℝ → Prop

/-- Weak convergence of the distributional derivatives of the indicator
functions: $D\chi_{\Omega(t_i)} \to D\chi_{\Omega(t_0)}$ in the sense of
measures along the min-max sequence.

**Ground truth**: Simon 1983 §13–§14 (weak measure convergence of
distributional derivatives for BV indicators); Maggi 2012, Theorem 12.15. -/
opaque DChiWeakConverge : Sweepout M → ℝ → Prop

/-- Perimeter convergence along the min-max sequence:
$\mathrm{Per}(\Omega(t_i)) \to \mathrm{Per}(\Omega(t_0))$.

By `minmax_mass_eq_width`, every min-max varifold limit $V$ has total
mass $\|V\|(M) = W(\Phi)$, so along any min-max sequence $t_i \to t_0$
the perimeters $\mathrm{Per}(\Omega(t_i)) = \mathbf{M}(|\partial^*\Omega(t_i)|)
\to \|V\|(M) = W$. The convergence to $\mathrm{Per}(\Omega(t_0))$ then
asserts $\|V\|(M) = \mathrm{Per}(\Omega(t_0))$ for every min-max varifold
limit—at the predicate level, this is the encoding below.

This unfolds the opaque convergence content of paper §6.1 line 1 in a
form that is directly provable from `NoMassCancellation` and
`minmax_mass_eq_width`. -/
def PerimeterConverge (Φ : Sweepout M) (t₀ : ℝ) : Prop :=
  ∀ V : Varifold M, MinMaxLimit Φ t₀ V →
    Varifold.mass V = ((Φ.slice t₀).perim : ℝ)

/-! ## Structural facts -/

/-- The total varifold mass of a min-max limit equals the width.
Provable directly by unfolding the `MinMaxLimit` definition. -/
theorem minmax_mass_eq_width {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (h : MinMaxLimit Φ t₀ V) : Varifold.mass V = width Φ := by
  obtain ⟨_, _, _, _, hmass⟩ := h
  exact hmass

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

/-! ## Existence of a min-max limit -/

/-- **Existence of a critical parameter and varifold limit (paper Proposition 3.7,
[CL03, Proposition 1.4]).**

For a non-excessive ONVP sweepout $\Phi$ with positive width, the standard
pull-tight argument produces a critical parameter $t_0 \in \mathfrak{m}(\Phi)$
and a varifold $V$ such that there is a min-max sequence $t_i \to t_0$ along
which $|\partial^*\Omega_{t_i}| \to V$.

This is a black-box wrapper for the CLS22 / Colding–De Lellis pull-tight
construction. -/
theorem exists_minmaxLimit
    {Φ : Sweepout M} (hne : NonExcessive Φ) (honvp : ONVP Φ) (hW : 0 < width Φ) :
    ∃ (t₀ : ℝ) (V : Varifold M), Critical Φ t₀ ∧ MinMaxLimit Φ t₀ V := by sorry

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
