import AltRegularity.MainTheorem

/-!
# AltRegularity.MinMaxExistence

End-to-end existence corollary for closed embedded smooth minimal
hypersurfaces via the ONVP non-excessive route, mirroring the assembly
of paper Theorem 1.1 from CLS22 Theorem 2.2 and the regularity chain.

## Paper narrative

The paper's overall narrative is the alternative-route version of the
classical existence theorem for closed minimal hypersurfaces:

  > **Existence of closed embedded smooth minimal hypersurfaces.**
  > Let $(M^{n+1}, g)$ be a closed Riemannian manifold with $2 \le n \le 6$.
  > There exists a smooth, closed, embedded minimal hypersurface
  > $\Sigma \subset M$.

Classical proofs route through Almgren–Pitts + Schoen–Simon. The paper's
alternative route is:

  $$\text{CLS22 Theorem 2.2 (existence of non-excessive ONVP)} +
    \text{paper Theorem 1.1 (regularity)}.$$

In the no-mass-cancellation case, this gives unconditional existence; in
the mass-cancellation case, regularity is conditional on Conjecture 5.9
(the sweepout-wide replacement). This file packages both into a single
existence statement.

## Chain logic

The corollary `exists_smoothMinimalHypersurface_via_ONVP` chains:

  1. `Sweepout.exists_nonExcessive_ONVP` ([CLS22, Theorem 2.2])
     produces a non-excessive ONVP sweepout $\Phi$.
  2. `Sweepout.exists_minmaxLimit` (paper Proposition 3.7,
     [CL03, Proposition 1.4]) produces a critical parameter $t_0$ and
     a varifold limit $V$.
  3. `Sweepout.mass_cancellation_or_no` (proven dichotomy) splits on
     whether $t_0$ exhibits mass cancellation.
       * No-cancellation case: `main_theorem_no_cancellation` gives
         smoothness unconditionally.
       * Cancellation case: `main_theorem_with_cancellation` gives
         smoothness conditional on
         `∀ p, SweepoutWideReplacement Φ t₀ V p` (Conjecture 5.9).

This chain is fully `Lean`-checked; the only sorries are at the input
boundary (CLS22 Theorem 2.2, CL03 pull-tight, etc.).
-/

namespace AltRegularity

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **End-to-end existence of a smooth minimal hypersurface (paper Theorem 1.1
applied to CLS22 Theorem 2.2).**

For a closed Riemannian manifold $M$ (modeled here as a compact metric
measure space), there exist:
  * a non-excessive ONVP sweepout $\Phi$ ([CLS22, Theorem 2.2]),
  * a critical parameter $t_0 \in \mathfrak{m}(\Phi)$,
  * a min-max varifold limit $V$ at $t_0$,

such that one of the two cases of paper Theorem 1.1 holds:
  * **No mass cancellation:** $V$ is a smooth closed embedded minimal
    hypersurface (unconditional, paper Theorem 1.1(a)).
  * **Mass cancellation:** $V$ is a smooth closed embedded minimal
    hypersurface conditional on the sweepout-wide replacement
    (Conjecture 5.9), invoked via
    `∀ p, SweepoutWideReplacement Φ t₀ V p`.

This statement is the alternative-route version of the classical
existence theorem for closed minimal hypersurfaces, going through the
ONVP framework + Wickramasekera regularity rather than Almgren–Pitts +
Schoen–Simon. -/
theorem exists_smoothMinimalHypersurface_via_ONVP
    [CompactSpace M]
    (n : ℕ) (hn : 2 ≤ n) (hn6 : n ≤ 6) :
    ∃ (Φ : Sweepout M) (t₀ : ℝ) (V : Varifold M),
      Sweepout.NonExcessive Φ ∧ Sweepout.ONVP Φ ∧
      Sweepout.Critical Φ t₀ ∧ Sweepout.MinMaxLimit Φ t₀ V ∧
      ((Sweepout.NoMassCancellation Φ t₀ ∧
          Varifold.IsSmoothMinimalHypersurface V)
       ∨
       (Sweepout.MassCancellation Φ t₀ ∧
          ((∀ p, SweepoutWideReplacement Φ t₀ V p) →
            Varifold.IsSmoothMinimalHypersurface V))) := by
  -- (1) CLS22 Theorem 2.2 (paper §3 thm:non-excessive-existence):
  -- get a non-excessive ONVP sweepout, using paper's 2 ≤ n ≤ 6 hypothesis.
  -- The cited theorem returns the paper-faithful `NonExcessiveStrict`;
  -- bridge to the framework's `NonExcessive` via `nonExcessive_of_strict`.
  obtain ⟨Φ, hneStrict, honvp, hW⟩ := Sweepout.exists_nonExcessive_ONVP M n hn hn6
  have hne : Sweepout.NonExcessive Φ := Sweepout.nonExcessive_of_strict hneStrict
  -- (2) Pull-tight: get a critical parameter t₀ and varifold limit V.
  obtain ⟨t₀, V, hcrit, hlim⟩ := Sweepout.exists_minmaxLimit hne honvp hW
  -- (3) Dichotomy on mass cancellation.
  refine ⟨Φ, t₀, V, hne, honvp, hcrit, hlim, ?_⟩
  rcases Sweepout.mass_cancellation_or_no Φ t₀ with hcanc | hno
  · -- Cancellation case: regularity conditional on the sweepout-wide replacement.
    right
    refine ⟨hcanc, ?_⟩
    intro hRep
    exact main_theorem_with_cancellation n hn hn6 hne honvp hcrit hlim hcanc hRep
  · -- No-cancellation case: regularity unconditional.
    left
    exact ⟨hno, main_theorem_no_cancellation n hn hn6 hne honvp hcrit hlim hno⟩

end AltRegularity
