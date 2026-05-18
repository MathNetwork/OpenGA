import OpenGALib.Riemannian.Metric.RiemannianMetric

/-!
# (Stub) Polymorphic metric notation file

Previously hosted `⟪·, ·⟫_g` and `‖·‖²_g` polymorphic dispatch notations
together with their `MetricInnerHom` / `MetricNormSq` typeclass plumbing.
Both notations and their dispatch classes have been dropped in favor of
explicit `g.metricInner` / `frobeniusSq` / Pi-form expansions, in line with
the explicit-`g` cascade (umbrella #9). The file is retained as an import
stub for now to avoid breaking the import graph; it can be deleted once
all imports of `OpenGALib.Riemannian.Util.MetricNotation` are removed.
-/
