import OpenGALib.Util.Attributes

/-!
# Riemannian tactic infrastructure

Re-exports the simp-set declarations from `Util/Attributes.lean`
together with the tagged metric algebra lemmas. Import this file to
use the simp sets without pulling in attribute machinery separately.

Simp sets:
  * `metric_simp` — `metricInner` algebra normalisation
  * `riem_simp`   — `riemannCurvature` definitional expansion
    (paired with explicit `rw` of bracket-swap helpers since those
    rewrite loops are out of the simp set)

Tactics:
  * `riem_normalize` — `simp only [riem_simp]` shorthand
-/

/-- **`riem_normalize` tactic** — applies the `riem_simp` simp set to
normalise `riemannCurvature` expressions to their underlying
`∇∇ - ∇∇ - ∇_{[·,·]}` form. Equivalent to `simp only [riem_simp]`. -/
macro "riem_normalize" : tactic => `(tactic| simp only [riem_simp])
