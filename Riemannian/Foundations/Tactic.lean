import Riemannian.Foundations.Attributes
import Riemannian.Metric.Basic

/-!
# Riemannian tactic infrastructure

User-facing entry point for the framework's domain-specific simp
attributes. Re-exports `Foundations/Attributes.lean` so downstream
code can simply
```
import Riemannian.Foundations.Tactic
```
to obtain both the attribute declarations and (transitively) the
metric algebra lemmas tagged with them.

## Available simp sets

  * `metric_simp` — `metricInner` algebra normalisation. Tagged
    lemmas: `metricInner_zero_left/right`, `metricInner_neg_left/right`,
    `metricInner_sub_left/right`, `metricInner_self_nonneg`.

## Usage

```
example {g : RiemannianMetric I M} (x : M) (V : TangentSpace I x) :
    metricInner x (V - 0) (-V + V) = -metricInner x V V + metricInner x V V := by
  simp only [metric_simp]
```

## Future extensions (deferred)

  * `koszul_simp` — Koszul algebraic identities.
  * `riem_simp` — Riemann tensor algebra.
  * `metric_calc` — bespoke tactic combining `metric_simp` with `ring`
    for closed-form algebraic goals.
-/
