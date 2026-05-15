# OpenGA Conventions

Canonical conventions for every mathematical object in OpenGALib. Each entry
cites the textbook source of the chosen convention. **Conventions are
non-negotiable: once anchored, they are fixed.** Disagreements about
convention are answered by citation, not by re-argument.

This document is updated whenever a new convention is anchored. The Lean
source is authoritative when prose and code disagree.

## v1 — Stage I (Layer 1 foundations)

This is the founding-phase conventions document. Subsequent stages append
sections; existing sections only ever clarify, never change semantics.

---

## Layer 1: Autonomy policy

The Layer 1 stack (`OpenGALib/Core/`) — `MetricMeasureSpace`, `LengthSpace`,
`GeodesicSpace` — is OpenGA-owned. Types, classes, headline statements, and
conventions are chosen for OpenGA's purposes; they are not constrained to
match upstream Mathlib formulations even where Mathlib has a similar
primitive. Mathlib tools (`eVariationOn`, `hausdorffMeasure`,
`IsRiemannianManifold`, …) are consumed directly when available, but always
through an OpenGA-namespace wrapper that fixes the OpenGA-side signature.

We do **not** copy Mathlib infrastructure wholesale. We do **not** re-export
Mathlib symbols under aliases. Each OpenGA Layer 1 primitive earns its
existence by carrying a distinct conceptual signature (intrinsic-metric
length functional; metric-measure triple as data; geodesic existence
predicate); when the OpenGA signature happens to coincide with a Mathlib
primitive, we use that Mathlib primitive in the body without re-defining it.

Ground truth: design philosophy §5.1 of the OpenGA charter / manifesto.

---

## Curvature sign convention

OpenGA uses the **do Carmo** sign convention throughout the Riemannian and
Comparison layers:

$$R(X, Y) Z = \nabla_X \nabla_Y Z - \nabla_Y \nabla_X Z - \nabla_{[X, Y]} Z.$$

Ricci curvature is the trace of $R(\,\cdot\,, Y) Z$ in its first slot;
sectional curvature of a 2-plane spanned by $X, Y$ is

$$K(X, Y) = \frac{\langle R(X, Y) Y, X \rangle}{\langle X, X \rangle \langle Y, Y \rangle - \langle X, Y \rangle^2}.$$

Ground truth: do Carmo, *Riemannian Geometry*, Ch. 4 §2 (definition of $R$),
Ch. 4 §3 (Ricci and sectional curvatures). This is the convention used by
Petersen, Cheeger–Ebin, and the majority of the geometric-analysis
literature (modulo a sign flip in the curvature-of-a-distribution
discussion, which is irrelevant for OpenGA's intended scope).

Implementation: `OpenGALib/Riemannian/Curvature/RiemannCurvature.lean`.

---

## Length functional

The length of a continuous path in a pseudo-extended-metric space is the
metric-side total variation:

$$\operatorname{pathLength}(\gamma) := \operatorname{eVariationOn}(\gamma, [0, 1]).$$

Ground truth: Burago–Burago–Ivanov, *A Course in Metric Geometry*, §2.1
(length as supremum of partition sums of distances).

This is OpenGA's canonical "length" primitive. It does not reference any
smooth structure on the target space, so it applies uniformly to metric
spaces, Riemannian manifolds (via the
`OpenGALib/Bridges/RiemannianToLength` bridge), Alexandrov spaces, and
limits of these.

Implementation: `OpenGALib.pathLength` in `OpenGALib/Core/LengthSpace.lean`,
wrapping Mathlib's `eVariationOn`.

The Mathlib tangent-integral length `Manifold.pathELength` (used inside
`IsRiemannianManifold`) is a *separate* concept and lives only at the
Riemannian boundary. Equality of the two on `C¹` paths over Riemannian
manifolds is the content of the `IsRiemannianManifold.toLengthSpace`
bridge.

---

## Geodesic existence

A `GeodesicSpace` is a length space in which the path-length infimum is
attained between every pair of points. The class only asserts existence —
neither uniqueness nor regularity is part of the OpenGA definition.

Ground truth: Burago–Burago–Ivanov §2.5.5.

The Hopf–Rinow theorem (complete Riemannian manifolds are geodesic spaces)
belongs to Layer 3a; it is not provided in Layer 1 as Layer 1 is
metric-only.

Implementation: `OpenGALib.GeodesicSpace` in
`OpenGALib/Core/GeodesicSpace.lean`.

---

## Metric measure space

A `MetricMeasureSpace M` is a `structure` carrying a `PseudoEMetricSpace M`
together with a `MeasureTheory.Measure M`. The metric and measure are stored
as data (not as typeclasses) so that a single carrier may host multiple
metric-measure structures.

Ground truth: Gromov, *Metric Structures for Riemannian and Non-Riemannian
Spaces*, §3¹⁄₂.5 (mm-spaces); Burago–Burago–Ivanov §1.7.

No regularity / σ-finiteness / Radon hypotheses are baked into the
structure. Stronger hypotheses are added at the use site, matching Mathlib's
`MeasureTheory.Measure` discipline.

Implementation: `MetricMeasureSpace` in
`OpenGALib/Core/MetricMeasureSpace.lean`.

---

## Future sections (Stage II and later)

To be appended:

* **Pointed Gromov–Hausdorff convergence**: base point convention, proper
  metric space hypothesis, ε–δ formulation. Anchored on Gromov §3 (proper
  metric spaces) and Burago–Burago–Ivanov Ch. 7.
* **Hausdorff measure notation**: `OpenGA.hausdorffMeasure d` wrapping
  Mathlib's `MeasureTheory.Measure.hausdorffMeasure`. Anchored on Mattila §4.
* **Tangent cones**: rescaled-ball Gromov–Hausdorff limits, base point at
  the singularity, Gromov–Hausdorff topology on isometry classes.
* **CD(K, N) / RCD(K, N) frameworks** when Layer 2 lands.
