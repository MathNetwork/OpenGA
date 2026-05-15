import OpenGALib.Core.GeodesicSpace
import OpenGALib.Core.LengthSpace
import OpenGALib.Core.MetricMeasureSpace
import OpenGALib.Core.Examples.EuclideanSpace

/-!
# OpenGA Core (Layer 1)

The foundational types of OpenGA, sitting directly above Mathlib's metric and
measure-theory infrastructure. Layer 1 supplies the three concepts on which
the entire library hangs:

* `MetricMeasureSpace` — the ambient `(M, d, μ)` triple of modern geometric
  analysis;
* `LengthSpace` — intrinsic-distance metric spaces (distance equals infimum of
  path lengths), with `pathLength` wrapping Mathlib's `eVariationOn`;
* `GeodesicSpace` — length spaces in which the infimum is attained.

Higher layers (synthetic curvature in Layer 2, smooth Riemannian in Layer 3a,
GMT in Layer 3c, applications in Layer 4) consume these concepts as ambient
hypotheses, with explicit `Bridges/` instances translating between the
metric-side and the Riemannian / GMT views.

Ground-truth references for Layer 1: Burago–Burago–Ivanov, *A Course in Metric
Geometry*; Gromov, *Metric Structures for Riemannian and Non-Riemannian
Spaces*.
-/
