import OpenGALib.MetricGeometry.GeodesicSpace
import OpenGALib.MetricGeometry.LengthSpace
import OpenGALib.MetricGeometry.MetricMeasureSpace
import OpenGALib.MetricGeometry.Examples.EuclideanSpace

/-!
# OpenGA MetricGeometry (Layer 1)

Foundational metric-geometry types: `MetricMeasureSpace` (Gromov `mm`-space),
`LengthSpace` (intrinsic distance = inf path length, `pathLength` wrapping
`eVariationOn`), `GeodesicSpace` (length space with infimum attained).

Ground truth: Burago–Burago–Ivanov, *A Course in Metric Geometry*;
Gromov, *Metric Structures for Riemannian and Non-Riemannian Spaces*.
-/
