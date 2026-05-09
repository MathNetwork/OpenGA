import OpenGALib.Util.Attributes
import OpenGALib.Riemannian.Metric.Basic

/-!
# Riemannian tactic infrastructure

User-facing entry point for the framework's domain-specific simp
attributes. Re-exports `Util/Attributes.lean` so downstream
code can simply
```
import OpenGALib.Util.Tactic
```
to obtain both the attribute declarations and (transitively) the
metric algebra lemmas tagged with them.

## Available simp sets

  * `metric_simp` — `metricInner` algebra normalisation. Tagged
    lemmas: `metricInner_zero_left/right`, `metricInner_neg_left/right`,
    `metricInner_sub_left/right`, `metricInner_add_left/right`,
    `metricInner_smul_left/right`, `metricInner_self_nonneg`.

  * `riem_simp` — `riemannCurvature` algebra normalisation. Currently
    populated by `riemannCurvature_def` (definitional expansion to
    `∇∇ - ∇∇ - ∇_{[·,·]}` form, no smoothness hypotheses). Use with
    explicit `rw` of the bracket-swap helper
    `covDeriv_mlieBracket_swap_apply` (kept out of the simp set to
    avoid `X ↔ Y` rewrite loops) and `abel` to close Riemann-tensor
    algebraic identities.

## Tactics

  * `riem_normalize` — shorthand for `simp only [riem_simp]`. Use as a
    first step on goals involving `riemannCurvature`; pair with explicit
    `rw` of named bracket / linearity lemmas as needed.

## Usage

```
example {g : RiemannianMetric I M} (x : M) (V : TangentSpace I x) :
    metricInner x (V - 0) (-V + V) = -metricInner x V V + metricInner x V V := by
  simp only [metric_simp]

example (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    riemannCurvature X Y Z x = -riemannCurvature Y X Z x := by
  riem_normalize
  rw [covDeriv_mlieBracket_swap_apply]
  abel
```

## Future extensions (deferred)

  * `koszul_simp` — Koszul algebraic identities.
  * `metric_calc` — bespoke tactic combining `metric_simp` with `ring`
    for closed-form algebraic goals.
-/

/-- **`riem_normalize` tactic** — applies the `riem_simp` simp set to
normalise `riemannCurvature` expressions to their underlying
`∇∇ - ∇∇ - ∇_{[·,·]}` form. Equivalent to `simp only [riem_simp]`. -/
macro "riem_normalize" : tactic => `(tactic| simp only [riem_simp])
