# `Riemannian/Util/` — engineering tax for the Riemannian layer

Per OpenGA's anchor-purity discipline (CLAUDE.md §"Engineering tax encapsulation"),
anchor files expose only `**Math.**`-tagged declarations; all `**Eng.**` and
`**Mixed.**` plumbing supporting those proofs lives here. Files inside `Util/`
are content-named — the folder name carries the `Util` role; individual files
describe their concrete content. No `Helpers` / `Base` / `Foundation` suffixes.

## Files, grouped by theme

### Chart Jacobian (smoothness of chart-frame derivatives)

| File | Role |
|------|------|
| [`ChartJacobianSmooth.lean`](./ChartJacobianSmooth.lean) | **Smoothness of chart-Jacobian-related continuous linear map-valued functions**: CLM-valued composites (e.g. `(triv α).symmL ℝ b`, `(triv α).continuousLinearMapAt ℝ b`) in `inTangentCoordinates` form. CLM-level operators. |
| [`ChartJacobianSmoothness.lean`](./ChartJacobianSmoothness.lean) | **Smoothness of chart-Jacobian matrix entries**: scalar-valued entries obtained by composing the CLM with model-basis vectors and projections. Scalar-level. |
| [`FlatChartDerivs.lean`](./FlatChartDerivs.lean) | **Tangent bundle — chart-derivative engineering**: `mfderiv` of chart maps under the flat (Euclidean-modeled) setup. |

### Tangent bundle / section glue

| File | Role |
|------|------|
| [`TangentHelpers.lean`](./TangentHelpers.lean) | **Tangent helpers — chart-bundle smoothness bridges**: general-purpose smoothness lemmas for chart-induced tangent-bundle constructions. |
| [`TangentSpaceInstances.lean`](./TangentSpaceInstances.lean) | **Typeclass instances on `TangentSpace I x` and the tangent bundle**: `instFiniteDimensionalTangent` (def-eq lift of `FiniteDimensional ℝ E`); `instRiemannianBundleOfHasMetric` (activates Mathlib's scoped fibre instances when `[HasMetric I M]` is in scope). |
| [`TensorBundleCoercions.lean`](./TensorBundleCoercions.lean) | **Riemannian (r,s)-tensor bundle — fiber-to-model coercion algebra**: coercion-level lemmas for `Tensor⟨r,s⟩` bundle. |
| [`MfderivApplySection.lean`](./MfderivApplySection.lean) | **Smoothness of `mfderiv f` applied to a tangent-bundle section**: machinery for proving that `(mfderiv f x).comp (v x)` is smooth when `f, v` are. |

### Metric inner / Riesz / notation

| File | Role |
|------|------|
| [`MetricNotation.lean`](./MetricNotation.lean) | **Polymorphic metric notation `⟪·, ·⟫_g` and `‖·‖²_g`**: dispatches over tangent-vector vs. section forms via `MetricInnerHom` / `MetricNormSq` typeclasses, resolved through `[HasMetric I M]`. |
| [`MetricInnerSmoothness.lean`](./MetricInnerSmoothness.lean) | **`metricInner` smoothness — pointwise / set / global variants**: `ContMDiffWithinAt` / `ContMDiff` / `MDifferentiable` parity siblings of the headline `metricInner_contMDiffWithinAt` in `Metric/RiemannianMetric.lean`. |
| [`MetricRieszBilinForm.lean`](./MetricRieszBilinForm.lean) | **Bridge from `RiemannianMetric.inner` to `BilinearForm.Form ℝ E`**: `toBilinForm`, `toBilinForm_isPosDef`. Supports the Riesz duality methods in `Metric/RiemannianMetric.lean`. |
| [`CotangentFunctional.lean`](./CotangentFunctional.lean) | **Half-Koszul cotangent functional**: bilinear-form construction in the Koszul formula. |

### Covariant derivative

| File | Role |
|------|------|
| [`CovDerivBridges.lean`](./CovDerivBridges.lean) | **`covDeriv` / `covDerivAt` simp bridges**: definitional unfolding lemmas. |
| [`CovDerivSmoothness.lean`](./CovDerivSmoothness.lean) | **Tensoriality + smoothness machinery for `koszulCovDeriv`**: the proof-level workhorse behind Levi-Civita smoothness. |

### Operator simp lemmas

| File | Role |
|------|------|
| [`ConnectionLaplacianSimp.lean`](./ConnectionLaplacianSimp.lean) | **Connection Laplacian — simp def-unfold**: `@[simp]` lemmas exposing the definitional shape of `Δ_g` for use in `rw` and `simp` calls. |
| [`DivergenceSimp.lean`](./DivergenceSimp.lean) | **Divergence — simp def-unfold**: same pattern for the manifold divergence operator. |

## Conventions

* **Math/Eng/Mixed tag** — every declaration begins its docstring with one of
  `**Math.**`, `**Eng.**`, `**Mixed.**`. `Util/` files are predominantly
  `**Eng.**` (engineering plumbing) and `**Mixed.**` (math statement on top of
  engineering proof body); occasional `**Math.**` declarations are the math
  parity variants that match `Metric/`-anchor-headline statements at a
  different smoothness parameter.
* **No `set_option linter.xxx false`** — linter regressions are fixed at the
  declaration level via `omit [...] in <decl>` or proper refactor, never by
  blanket disable.
* **Anchor purity** — anchor files in sibling folders (`Connection/`,
  `Curvature/`, `Metric/`, `Operators/`, `Volume/`, `TensorBundle/`,
  `Instances/`, `Manifold/`) expose only `**Math.**`. Anything else lands
  here.
