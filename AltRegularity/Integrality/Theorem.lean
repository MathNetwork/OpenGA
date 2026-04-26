import AltRegularity.Integrality.ReducedBoundary
import AltRegularity.Integrality.PerimeterConvergence
import AltRegularity.Sweepout.MassCancellation
import AltRegularity.Regularity.AlphaStructural

/-!
# AltRegularity.Integrality.Theorem

Integrality of the limit varifold (Theorem 6.1 of the paper).

For a non-excessive ONVP sweepout $\Phi$ with min-max sequence $t_i \to t_0$
and varifold limit $V = \lim |\partial^*\Omega_{t_i}|$:

  * **(a) No mass cancellation case.** If $\mathrm{Per}(\Omega_{t_0}) = W$,
    then $V = |\partial^*\Omega_{t_0}|$ is integral with multiplicity 1
    (via perimeter convergence and the De Lellis–Tasnady criterion).

  * **(b) Mass cancellation case (conditional).** If $\mathrm{Per}(\Omega_{t_0}) < W$,
    then $\|V\| \ge |D\chi_{\Omega_{t_0}}|$ pointwise (Lemma 6.4); on the
    cancelled mass $\mu_{\mathrm{c}} = \|V\| - |D\chi_{\Omega_{t_0}}|$, integrality
    is conditional on positive density on $\mathrm{spt}\,\mu_{\mathrm{c}}$
    (Section 5.1, `AltRegularity.PositiveDensity`).
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [MeasureTheory.MeasureSpace M]

/-- **Integrality, no-mass-cancellation case (Theorem 6.1(a)).**

Formalization of paper §6.1 Theorem 6.3's 5-line proof:

  > "Since $\Phi$ is continuous in the flat topology, $\Omega(x_i) \to \Omega(x_0)$
  > in $L^1(M)$, so $D\chi_{\Omega(x_i)} \to D\chi_{\Omega(x_0)}$ weakly as
  > measures. Moreover, the no-mass-cancellation hypothesis gives
  > $\mathrm{Per}(\Omega(x_i)) \to \mathrm{Per}(\Omega(x_0))$. Both conditions
  > of Proposition 6.1 are satisfied, so $V = |\partial^*\Omega(x_0)|$ is the
  > integral varifold induced by the Caccioppoli boundary $\partial^*\Omega(x_0)$."

The 5 lemma applications mirror the 5 paper lines:
  (a) flat continuity → L¹ convergence;
  (b) L¹ → weak measure convergence;
  (c) no mass cancellation → perimeter convergence;
  (d) DLT criterion (Proposition 6.1): both convergence conditions
      identify $V = |\partial^*\Omega(t_0)|$;
  (e) the boundary varifold of any finite-perimeter set is integral.
-/
theorem integrality_no_cancellation
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hlim : Sweepout.MinMaxLimit Φ t₀ V)
    (hno : Sweepout.NoMassCancellation Φ t₀) :
    Varifold.IsIntegral V := by
  -- (a) Flat-continuity of Φ gives L¹ convergence of slice carriers.
  have hL1 := Sweepout.l1Convergence_of_minmaxLimit hlim
  -- (b) L¹ convergence of indicators gives weak convergence of D χ.
  have hWeak := Sweepout.dChiWeak_of_l1 hL1
  -- (c) No mass cancellation gives perimeter convergence.
  have hPer := Sweepout.perimeterConvergence_of_noMassCancellation hlim hno
  -- (d) DLT criterion: V is the boundary varifold of the limit slice.
  have hVeq : V = Varifold.ofBoundary (Φ.slice t₀) := dlt_criterion hlim hWeak hPer
  -- (e) The boundary varifold is integral.
  rw [hVeq]
  exact Varifold.isIntegral_ofBoundary _

/-- **Integrality, mass-cancellation case (Theorem 6.1(b)), conditional on
positive density on the support of the cancelled mass.** -/
theorem integrality_with_cancellation
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hlim : Sweepout.MinMaxLimit Φ t₀ V)
    (hcanc : Sweepout.MassCancellation Φ t₀)
    (hposDensity : ∀ p ∈ Varifold.support V, 0 < Varifold.density V p) :
    Varifold.IsIntegral V := by sorry

end AltRegularity
