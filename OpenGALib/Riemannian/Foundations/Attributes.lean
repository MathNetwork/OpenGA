import Mathlib.Tactic.Common

/-!
# Riemannian simp attributes — declarations

Pure attribute registration, intentionally without imports of lemmas
that consume the attributes. This file is imported by lemma sites
(e.g., `Metric/Basic.lean`) to make `[metric_simp]` available as a
tag, and by downstream proof code to invoke `simp [metric_simp]`.

Splitting attribute registration from lemma sites avoids a circular
import (lemma sites need the attribute declared; a Tactic-level docs
file would otherwise need to import the lemma sites for documentation
context).
-/

/-- Simp set for `metricInner` algebra normalisation: bilinearity, sign
rules, zero / neg / sub / self_nonneg. Tagged on the lemmas in
`Metric/Basic.lean`; downstream proofs can invoke
`simp only [metric_simp]` for routine inner-product calculations. -/
register_simp_attr metric_simp
