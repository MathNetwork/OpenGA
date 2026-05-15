# OpenGA Conventions

Canonical conventions, each with textbook source. **Non-negotiable once anchored** — disagreements are answered by citation. The Lean source is authoritative when prose and code disagree.

## Curvature sign

OpenGA uses do Carmo's convention throughout Riemannian and Comparison:

$$R(X, Y) Z = \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z.$$

Ricci is the trace of $R(\,\cdot\,, Y) Z$ in its first slot; sectional curvature of the 2-plane spanned by $X, Y$ is

$$K(X, Y) = \frac{\langle R(X, Y) Y, X \rangle}{\langle X, X \rangle \langle Y, Y \rangle - \langle X, Y \rangle^2}.$$

Ground truth: do Carmo, *Riemannian Geometry*, Ch. 4 §2–§3. Same convention as Petersen and Cheeger–Ebin.

Implementation: `OpenGALib/Riemannian/Curvature/RiemannCurvature.lean`.

## Length functional

Length of a continuous path in a pseudo-extended-metric space is the metric-side total variation:

$$\operatorname{pathLength}(\gamma) := \operatorname{eVariationOn}(\gamma, [0, 1]).$$

Ground truth: Burago–Burago–Ivanov §2.1.

Applies uniformly to metric spaces, Riemannian manifolds (via `Bridges/RiemannianToLength`), Alexandrov spaces, and limits. The Mathlib tangent-integral length `Manifold.pathELength` (used inside `IsRiemannianManifold`) is a *separate* concept; equality on `C¹` paths is the content of `IsRiemannianManifold.toLengthSpace`.

Implementation: `OpenGALib.pathLength` in `OpenGALib/MetricGeometry/LengthSpace.lean`, wrapping `eVariationOn`.

## Geodesic existence

`GeodesicSpace` = length space in which the path-length infimum is attained between every pair of points. Existence only — neither uniqueness nor regularity is part of the definition.

Ground truth: Burago–Burago–Ivanov §2.5.5. Hopf–Rinow (complete Riemannian ⇒ geodesic) belongs to Layer 3a; Layer 1 is metric-only.

Implementation: `OpenGALib.GeodesicSpace` in `OpenGALib/MetricGeometry/GeodesicSpace.lean`.

## Metric measure space

`MetricMeasureSpace M` = `structure` carrying a `PseudoEMetricSpace M` together with a `MeasureTheory.Measure M`. Both stored as data (not typeclasses), so a single carrier may host multiple metric-measure structures. No regularity / σ-finiteness / Radon hypotheses baked in — added at the use site, matching Mathlib's `MeasureTheory.Measure` discipline.

Ground truth: Gromov §3¹⁄₂.5 (mm-spaces); Burago–Burago–Ivanov §1.7.

Implementation: `MetricMeasureSpace` in `OpenGALib/MetricGeometry/MetricMeasureSpace.lean`.
