#!/usr/bin/env python3
"""Prepare attributed publication payloads for the closed-surface area proof."""
import json
from pathlib import Path
from export_closed_surface import Export, DIRECTORY, REPOSITORY, ENVIRONMENT, SOURCE_REVISION, UPSTREAM_REVISION, digest, path_for

MEASURE = 'DifferentialGeometry.Integral.Measure.'
# Each description follows the actual source statement, including its hypotheses.
STATEMENTS = {
'chartLocal_weighted_finset_sum_eq_riemannianMeasure_integral': ('Weighted chart integrals recover the global integral', r"""On a compact Hausdorff smooth real manifold, let $g_t$ be a smooth Riemannian metric and $h$ a continuous real function. For the chosen subordinate smooth partition of unity $(\rho_\alpha)$ and chart measures $\mu_{\alpha,t}$, $$\sum_\alpha\int h\rho_\alpha\,d\mu_{\alpha,t}=\int h\,d\mu_{g_t}.$$ The finite sum runs over the active partition indices. This identifies the local derivative terms with the global volume integral."""),
'volume_variation_formula_of_chart_derivs': ('Assembling explicit chart derivatives into volume variation', r"""On a compact Hausdorff smooth manifold, assume $f_s$ is continuous for times near $t$, the proposed derivative density $H_t=\partial_t f+\tfrac12\operatorname{tr}(g_t^{-1}\dot g_t)f_t$ is continuous, and every partition-weighted chart integral has derivative $\int H_t\rho_\alpha\,d\mu_{\alpha,t}$. Then $$\frac{d}{dt}\int f_t\,d\mu_{g_t}=\int H_t\,d\mu_{g_t}.$$ This is the assembly step; the chart derivative hypotheses are explicit."""),
'continuousOn_traceTimeDerivMetric_on_base': ('Joint continuity of the metric variation trace in a chart', r"""Let $g_s$ satisfy `MetricFamilyRegularAt`, including joint continuity of its chart Gram entries and their time derivatives on each entire chart-time domain. If $G_\alpha(s,x)$ is its Gram matrix in chart $\alpha$, then $$(s,x)\longmapsto\operatorname{tr}(G_\alpha(s,x)^{-1}\partial_sG_\alpha(s,x))$$ is continuous on $\mathbb R$ times the chart base. This supplies the local continuity used in differentiating volume."""),
'traceTimeDerivMetric_continuous': ('Continuity of the global metric variation trace', r"""For a family $g_s$ satisfying `MetricFamilyRegularAt` and a fixed time $t$, $$x\longmapsto\operatorname{tr}_{g_t}\dot g_t(x)$$ is continuous on the smooth manifold. The trace is the chart-independent quantity defined from the Gram matrix. This lets compactness provide the bounds needed for integration."""),
'per_chart_integrand_hasDerivAt': ('Derivative of the weighted chart density integrand', r"""Let $g_s$ satisfy `MetricFamilyRegularAt`, let $x$ lie in chart $\alpha$, and suppose $s\mapsto f(s,x)$ has derivative $\partial_t f(t,x)$ at $t$. For any fixed real weight $\rho(x)$ and chart density $J_s(x)$, $$\partial_t(f_t\rho J_t)=(\partial_t f_t+\tfrac12\operatorname{tr}_{g_t}\dot g_t\,f_t)\rho J_t.$$ No regularity of the weight is needed for this pointwise time derivative."""),
'continuousOn_chartDensity_family': ('Joint continuity of Riemannian chart densities', r"""For a smooth metric family satisfying `MetricFamilyRegularAt`, its chart density $J_\alpha(s,x)=\sqrt{\det G_\alpha(s,x)}$ is continuous on $\mathbb R$ times the chart base. Here $G_\alpha$ is the positive definite Gram matrix on that base. This is a regularity input to differentiation under the integral."""),
'per_chart_hasDerivAt': ('Differentiating a partition-weighted chart integral', r"""Let $M$ be a compact Hausdorff smooth real manifold. Suppose $g_s$ satisfies `MetricFamilyRegularAt` and $f_s$ satisfies `FunctionRegularAt` at $t$. For a chosen partition function $\rho_\alpha$, $$\frac{d}{dt}\int f_t\rho_\alpha\,d\mu_{\alpha,t}=\int(\partial_t f_t+\tfrac12\operatorname{tr}_{g_t}\dot g_t\,f_t)\rho_\alpha\,d\mu_{\alpha,t}.$$ The proof derives the local domination and measurability requirements from these regularity and compactness assumptions."""),
'hasDerivAt_setIntegral_model': ('Differentiation under a model-space integral', r"""Let $A$ be a set in a finite-dimensional real normed model space with its chosen Haar measure. Suppose $F(t,\cdot)$ is almost everywhere strongly measurable near $t_0$, $F(t_0,\cdot)$ is integrable, the proposed derivative $F'(t_0,\cdot)$ is measurable, and $|F'(t,y)|\le b(y)$ almost everywhere for all $t$ in a neighborhood of $t_0$, with $b$ integrable. If $\partial_tF=F'$ there, then $$\frac{d}{dt}\bigg|_{t=t_0}\int_A F(t,y)\,dy=\int_A F'(t_0,y)\,dy,$$ and the derivative integrand is integrable."""),
'deriv_chartGramMatrix_pullback': ('Time derivatives of Gram matrices under a chart change', r"""Let $g_s$ satisfy `MetricFamilyRegularAt`. At a point in the overlap of two chart bases, let $C$ be the time-independent transition matrix of their tangent bases and $G_0,G_1$ the metric Gram matrices. Then $$\dot G_1(t)=C^{T}\dot G_0(t)C.$$ This transfers the metric time derivative between charts."""),
'transitionMatrix_mul_reverse': ('Inverse transition matrices on a chart overlap', r"""At a point in the overlap of two tangent-bundle chart bases, the coordinate transition matrices satisfy $$C_{01}C_{10}=I.$$ They describe the same tangent vectors in the two chart-induced bases. This supplies the invertibility needed for invariance of the metric variation trace."""),
'integral_chart_ae': ('Real integration against a chart-local volume measure', r"""Let $g$ be a smooth Riemannian metric, $\alpha$ a chart, and $h$ almost everywhere strongly measurable for the chart-local measure. With $\phi_\alpha$ the extended chart and $J_\alpha$ its Riemannian density, $$\int h\,d\mu_\alpha=\int_{\phi_\alpha(U_\alpha)}J_\alpha(\phi_\alpha^{-1}y)h(\phi_\alpha^{-1}y)\,dy.$$ The statement uses Lean\'s Bochner integral, including its convention for nonintegrable functions."""),
'trace_chartGramMatrix_inv_deriv_chart_independent': ('Chart independence of the metric variation trace', r"""Let $g_s$ satisfy `MetricFamilyRegularAt`. For chart Gram matrices $G_0,G_1$ evaluated at a common point of their bases, $$\operatorname{tr}(G_0(t)^{-1}\dot G_0(t))=\operatorname{tr}(G_1(t)^{-1}\dot G_1(t)).$$ This makes the local determinant derivative a globally defined scalar."""),
'riemannianVolumeMeasure_eq_finset_sum': ('Finite partition-of-unity decomposition of Riemannian volume', r"""On a compact Hausdorff smooth real manifold with the stated sigma-compactness instance, let $g$ be a smooth Riemannian metric. Its chosen volume measure is $$\mu_g=\sum_{\alpha\in F}\rho_\alpha\mu_{\alpha,g},$$ where $F$ is the finite set of active indices of the subordinate smooth partition of unity. This is an equality of measures."""),
'integral_riemannianVolumeMeasure_eq_finset_sum': ('Finite decomposition of continuous Riemannian integrals', r"""On a compact Hausdorff smooth manifold with the stated sigma-compactness instance, for any continuous real function $h$ and smooth Riemannian metric $g$, $$\int h\,d\mu_g=\sum_{\alpha\in F}\int h\,d(\rho_\alpha\mu_{\alpha,g}).$$ The measures and active finite partition are those of the chosen atlas. This converts global integration into finitely many chart integrals."""),
'volume_variation_formula_of_chart_integrals': ('Global differentiation from finitely many chart integrals', r"""On a compact Hausdorff smooth manifold, assume $f_s$ is continuous near time $t$, each partition-weighted chart integral has derivative $I_\alpha$, and the finite sum of these derivatives equals $I$. Then $$\frac{d}{dt}\int f_t\,d\mu_{g_t}=I.$$ This theorem assembles chart derivatives without imposing a formula for them."""),
'hasDerivAt_chartDensityFamily_eq_half_trace_inv_mul': ('Derivative of a Riemannian chart density', r"""At a point of a tangent-bundle chart base, let $G(s)$ be the Gram matrix of a smooth Riemannian metric family. If its entries have derivatives given by the matrix $G'$ at $t$, then $$\frac{d}{dt}\sqrt{\det G(t)}=\tfrac12\operatorname{tr}(G(t)^{-1}G')\sqrt{\det G(t)}.$$ Positive definiteness comes from the metric and the chart base assumption."""),
'MetricFamilyRegularAt.of_chartGram_timeDeriv': ('Constructing metric-family regularity from chart derivatives', r"""Suppose every chart Gram entry $G_{ij}(t,x)$ of a smooth metric family has a time derivative $D_{ij}(t,x)$ for every real time on its chart base, and both $G_{ij}$ and $D_{ij}$ are jointly continuous there. Then the family satisfies `MetricFamilyRegularAt` at every specified time. This packages exactly those global chart-time hypotheses; it does not assert their existence for arbitrary metric families."""),
'FunctionRegularAt_const': ('Regularity of a constant integrand', r"""For every real constant $c$ and time $t_0$, the function $f(t,x)=c$ satisfies `FunctionRegularAt` at $t_0$, with time derivative zero. This specializes the variation of weighted integrals to variation of total volume."""),
'chartBasisVecFiber_pullback': ('Changing tangent chart bases', r"""At a point in the overlap of two tangent-bundle chart bases, the basis vectors satisfy $$e_i^{(1)}=\sum_k C_{ki}e_k^{(0)},$$ where $C$ is the transition matrix from the second basis to the first. This finite-dimensional basis identity is used to compare metric Gram matrices."""),
'chartGramMatrix_pullback_eq_sum': ('Gram matrix entries under a tangent basis change', r"""For a smooth Riemannian metric and two tangent chart bases at a common point, with transition matrix $C$, $$G^{(1)}_{ij}=\sum_{k,l}C_{ki}C_{lj}G^{(0)}_{kl}.$$ Equivalently, $G^{(1)}=C^TG^{(0)}C$. This is the bilinear change-of-basis identity."""),
'aemeasurable_chartDensity_symm_pullback': ('Measurability of chart density in model coordinates', r"""For a smooth Riemannian metric and extended chart $\phi_\alpha$, the nonnegative extended-real function $$y\longmapsto\operatorname{ofReal}(J_\alpha(\phi_\alpha^{-1}y))$$ is almost everywhere measurable for model Haar measure restricted to the chart target. This validates the density used to construct the chart-local volume measure."""),
'chartLocalMeasure_lintegral': ('Nonnegative integration against a chart-local volume measure', r"""For a measurable $F:M\to[0,\infty]$, smooth metric $g$ and extended chart $\phi_\alpha$, $$\int F\,d\mu_\alpha=\int_{\phi_\alpha(U_\alpha)}\operatorname{ofReal}(J_\alpha(\phi_\alpha^{-1}y))F(\phi_\alpha^{-1}y)\,dy.$$ Both sides are nonnegative extended-real integrals. This is the density-and-pushforward construction of the chart measure."""),
'hasDerivAt_sqrt_det_eq_half_trace_inv_mul': ('Jacobi formula for the square root of a positive determinant', r"""Let $G(s)$ be a real square matrix family indexed by a finite type. Suppose every entry has derivative $G'_{ij}$ at $t$ and $\det G(t)>0$. Then $$\frac{d}{dt}\sqrt{\det G(t)}=\tfrac12\operatorname{tr}(G(t)^{-1}G')\sqrt{\det G(t)}.$$ This is the algebraic derivative used for volume densities."""),
'hasDerivAt_det_of_entries': ('Differentiating the determinant entry by entry', r"""Let $G(s)$ be a real square matrix family on a finite index type, with entry derivatives $G'_{ij}$ at $t$. Then $$\frac{d}{dt}\det G(t)=\sum_\sigma\operatorname{sgn}(\sigma)\sum_kG'_{\sigma(k),k}\prod_{i\ne k}G_{\sigma(i),i}(t).$$ No invertibility assumption is required. The proof differentiates the finite Leibniz expansion."""),
'perm_sum_eq_trace_adjugate_mul': ('The determinant directional sum as an adjugate trace', r"""For real square matrices $A,B$ on a finite index type, $$\sum_\sigma\operatorname{sgn}(\sigma)\sum_k B_{\sigma(k),k}\prod_{i\ne k}A_{\sigma(i),i}=\operatorname{tr}(\operatorname{adj}(A)B).$$ This algebraic identity is valid even when $A$ is singular and connects the determinant expansion to Jacobi\'s formula."""),
'riemannianMeasure_compact_lt_top': ('Finiteness of Riemannian measure on compact sets', r"""Let $g$ be a smooth Riemannian metric on a Hausdorff smooth manifold and let $\rho$ be a smooth partition of unity subordinate to the atlas. For every compact set $K$, $$\mu_{g,\rho}(K)<\infty.$$ The proof uses local finiteness of the partition and chart-local finiteness. Compactness of the entire manifold is not assumed."""),
'chartLocalMeasure_compact_lt_top': ('Finiteness of a chart measure on compact subsets of its source', r"""Let $g$ be a smooth Riemannian metric on a Hausdorff smooth manifold. If $K$ is compact and contained in chart $\alpha$\'s source, then $$\mu_{\alpha,g}(K)<\infty.$$ The containment hypothesis is explicit. This provides the local measure bound needed to sum partition-weighted integrals."""),
'volume_variation_formula': ('Variation of integration against a smooth metric family', r"""On a compact Hausdorff smooth real manifold, assume `MetricFamilyRegularAt` for $g_s$ and `FunctionRegularAt` for $f_s$ at $t_0$. Then $$\frac{d}{dt}\bigg|_{t=t_0}\int f_t\,d\mu_{g_t}=\int\left(\partial_tf(t_0,x)+\tfrac12\operatorname{tr}_{g_{t_0}}\dot g_{t_0}(x)f(t_0,x)\right)d\mu_{g_{t_0}}.$$ The source regularity structures retain their full chart-time hypotheses. OpenGA separately proves the localization needed for a flow defined on an interval."""),
'chartBasisVec_contMDiffOn': ('Smoothness of chart-induced tangent vector fields', r"""Each tangent vector field induced by a fixed model basis vector through a tangent-bundle trivialization is smooth on that trivialization\'s base. This supplies smooth local frames for the chart Gram matrices of a smooth metric."""),
'chartGramMatrix_dotProduct_mulVec': ('The Gram quadratic form equals the metric norm square', r"""Let $G$ be the chart Gram matrix of a smooth metric $g$, and let $c_i$ be real coefficients. For the chart-induced vectors $e_i$, $$c^TGc=g\left(\sum_i c_ie_i,\sum_j c_je_j\right).$$ This bilinear identity holds with the chart-vector definitions used in the formal statement and proves positivity on the chart base."""),
'chartGramMatrix_posDef': ('Positive definiteness of metric Gram matrices on a chart base', r"""At a point of a tangent-bundle chart base, the Gram matrix of a smooth Riemannian metric in the induced tangent basis is positive definite. Consequently its determinant is positive and it is invertible. The base-membership assumption ensures that the chart vectors form a basis."""),
'chartGramMatrix_entry_contMDiffOn': ('Smoothness of metric Gram matrix entries', r"""For a smooth Riemannian metric, each entry of its Gram matrix in a tangent chart basis is a smooth real function on the chart base. This follows by evaluating the smooth metric on the smooth chart basis fields."""),
'chartGramMatrix_det_contMDiffOn': ('Smoothness of the metric Gram determinant', r"""For a smooth Riemannian metric, $$x\longmapsto\det G_\alpha(x)$$ is smooth on the tangent chart base. Here $G_\alpha$ is the Gram matrix in the chart-induced basis. The finite determinant expression preserves smoothness."""),
'DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.metricCLMSmoothAt': ('Local smoothness of a time-dependent metric as a bilinear-map section', r"""Let $g_t$ satisfy `MetricFamilySmoothOn` on a real time interval $D$. If $D.regular$ is a neighborhood of $t$, then the section $$(s,x)\longmapsto (g_s)_x$$ of continuous bilinear forms on tangent spaces is smooth at $(t,x)$. This converts the source tensor-family regularity into the bilinear-map form needed for pulling back a metric."""),
'OpenGA.RicciFlow.hasDerivAt_area': ('Area variation of a fixed closed immersed surface under Ricci flow', r"""Let $g_t$ be a smooth Ricci-flow solution on a regular time interval, in the precise sense of `SolutionOn` and `IsSolutionOn`. Let $N$ be a compact Hausdorff smooth two-dimensional manifold without boundary and $f:N\to M$ a fixed smooth immersion. Write $h_t=f^*g_t$ and let $d\mu_{h_t}$ be its actual Riemannian area measure. At every regular time, $$\frac{d}{dt}\operatorname{Area}_{g_t}(f)=-\int_N\operatorname{tr}_{h_t}(f^*\operatorname{Ric}_{g_t})\,d\mu_{h_t}.$$ Self-intersections are allowed; differential injectivity excludes branch points. The theorem derives metric regularity and differentiation under the integral from the stated geometric hypotheses. It supplies the smooth area-variation step for the finite-extinction route; minimality, Gauss-Bonnet and the branched-sphere estimate are separate steps."""),
'OpenGA.RicciFlow.inducedMetric_regularOn': ('Regularity of metrics induced by a smooth immersion along a metric family', r"""Let $g_t$ satisfy `MetricFamilySmoothOn` on a time interval $D$, and let $f:N\to M$ be a fixed smooth immersion of a Hausdorff smooth surface. Then $$h_t=f^*g_t$$ satisfies `MetricFamilyRegularOn` on $D.regular$. The latter records the time derivatives and joint continuity of the induced chart Gram entries on that set. Compactness and a Ricci-flow equation are not needed for this step."""),
'OpenGA.RicciFlow.traceTimeDeriv_inducedMetric': ('The induced metric variation trace equals minus twice the tangential Ricci trace', r"""Let $g_t$ be a smooth Ricci-flow solution and $f:N\to M$ a fixed smooth immersion of a Hausdorff surface, with $h_t=f^*g_t$. At every regular time and every $x\in N$, $$\operatorname{tr}_{h_t}\dot h_t(x)=-2\operatorname{tr}_{h_t}(f^*\operatorname{Ric}_{g_t})(x).$$ The ambient Ricci tensor is the actual contraction of the Levi-Civita curvature supplied by the solution, not an independent tensor assumption."""),
'OpenGA.MetricFamilyRegularOn.comp': ('Global metric-family regularity after a smooth time reparametrization', r"""Let $g_s$ satisfy `MetricFamilyRegularOn` on a set $U\subset\mathbb R$, and let $r:\mathbb R\to\mathbb R$ be smooth with $r(\mathbb R)\subset U$. Then the reparametrized family $$\widetilde g_s=g_{r(s)}$$ satisfies the source `MetricFamilyRegularAt` condition at each time. This enables a local-in-time metric family to use the global-in-time integral-variation theorem."""),
'OpenGA.hasDerivAt_totalRiemannianVolume': ('Local-in-time variation of total Riemannian volume', r"""Let $M$ be a compact Hausdorff smooth real manifold and $g_s$ a family of smooth Riemannian metrics satisfying `MetricFamilyRegularOn` on a neighborhood $U$ of $t$. Then $$\frac{d}{dt}\operatorname{Vol}(M,g_t)=\frac12\int_M\operatorname{tr}_{g_t}\dot g_t\,d\mu_{g_t}.$$ The measure and volume are the constructed Riemannian ones. A smooth localization of time removes the need to assume regularity at all real times."""),
}

DEFINITION_TITLES = {
'Analysis.TimeInterval': 'Regular time domains for geometric flows',
'Bundle.PartialMfderiv.Basic': 'Vertical derivatives of bundle-valued maps',
'Bundle.Section': 'Smooth bundle-section evaluation helpers',
'Bundle.SectionOperations': 'Smooth operations on bundle sections',
'Bundle.TangentSpace': 'Tangent-fiber and model-space linear equivalences',
'Geometry.Connection.MetricCompatibility': 'Metric compatibility of a covariant derivative',
'Geometry.Curvature.Basic': 'Curvature of a connection on tangent vector fields',
'Geometry.Curvature.Bochner.BochnerTensor': 'Smooth evaluation of tangent bilinear forms',
'Geometry.Metric.ChartGram': 'Chart tangent bases and metric Gram matrices',
'Tensor.Auxiliary.PredualBasis': 'Continuous dual bases in finite dimension',
'Tensor.Multilinear.Comp': 'Composition of continuous multilinear maps',
'Tensor.Multilinear.Tensor': 'Products of multilinear tensors',
'Tensor.Multilinear.Bundle': 'The vector bundle of continuous multilinear forms',
'Tensor.Multilinear.Basis': 'Finite-dimensional bases of multilinear forms',
'Tensor.Multilinear.Fiber': 'Model coordinates for multilinear tensor fibers',
'Tensor.Multilinear.BundleSmoothEvaluation': 'Smooth evaluation of multilinear bundle sections',
'Tensor.RSTensor.Derivation.NablaOnTensors': 'Chart-constant tangent fields for tensor differentiation',
'Tensor.RSTensor.NablaOnTensors.Connection.Smooth': 'Local smoothness of covariant derivatives',
'Tensor.RSTensor.NablaOnTensors.Connection.Tangent': 'Smoothness tests for tangent covariant derivatives',
'Tensor.RSTensor.Defs': 'Covariant and mixed tensor fibers',
'Tensor.RSTensor.Basis': 'Local bases for mixed tensor bundles',
'Tensor.RSTensor.Coordinates.Field': 'Covariant and mixed tensor fields',
'Tensor.RSTensor.CotangentRiemannian': 'Cotangent vectors as continuous linear functionals',
'Tensor.RSTensor.Derivation.Contract': 'Contractions of mixed tensor fields',
'Tensor.RSTensor.Field': 'Evaluation of mixed tensor fields',
'Tensor.RSTensor.LocalFrameRegularity': 'Smooth local frames for tensor bundles',
'Tensor.RSTensor.Metric': 'A Riemannian metric as a covariant tensor',
'Tensor.RSTensor.TangentMetric': 'Tangent metric data for tensor bundles',
'Tensor.RSTensor.FiberMetric.Tensor0SMetric': 'Metrics and norms on covariant tensor fibers',
'Tensor.RSTensor.MetricCompatibility': 'The metric tensor field',
'Analysis.Integration.Measure.ChartDensity': 'Riemannian chart densities and chart-local measures',
'Analysis.Integration.Measure.RiemannianMeasure': 'Volume measures from a subordinate partition of unity',
'Analysis.Integration.Measure.Invariance': 'Canonical atlas volume and tangent transition matrices',
'Analysis.Integration.Measure.FamilyDefs': 'Metric-family regularity and the volume-variation trace',
'Analysis.Integration.Measure.Properties': 'Chart measure finiteness helpers',
'Analysis.Integration.Measure.FamilyDecomposition': 'The finite active atlas partition on a compact manifold',
'Analysis.Integration.Measure.Family': 'Measurable-space instances for chart integral variation',
'Analysis.Integration.Measure.VolumeVariation': 'Regularity helpers for Riemannian volume variation',
'Geometry.Curvature.Riemann.Basic.Field': 'Tensoriality of connection curvature',
'Geometry.Curvature.Riemann.Basic.Pointwise': 'Pointwise Riemann and Ricci curvature',
'Geometry.Curvature.Riemann.Basic.Sections': 'Riemann and Ricci curvature sections',
'Geometry.Curvature.Tensor': 'Curvature tensor types and Ricci contraction',
'Geometry.Curvature.Metric': 'Curvature determined by a smooth Riemannian metric',
'Geometry.Metric.TensorInner.MetricFiberData': 'Metric duality on finite-dimensional fibers',
'Geometry.Metric.TensorInner.CotangentRiemannian': 'The metric induced on cotangent fibers',
'Geometry.Metric.Family.Basic': 'Smooth families of metrics and connections',
'Geometry.Operator.Gradient': 'Metric flat and sharp maps',
'Geometry.Operator.Operators': 'Metric duality and the gradient',
'Geometry.Operator.RoughLaplacian': 'Metric contraction of covariant tensors',
'Bundle.LocalFrameRegularity': 'Local-frame tests for smooth bundle homomorphisms',
'Geometry.Connection.LeviCivita.KoszulFormula': 'The Levi-Civita connection constructed from the Koszul formula',
'Geometry.Connection.LeviCivita.Basic': 'Torsion-free and metric-compatible connections',
'Geometry.Connection.LeviCivita.Smooth.MetricFlatBasis': 'Smooth local metric-dual bases',
'Geometry.Connection.LeviCivita.Smooth.Connection': 'Smoothness of the constructed Levi-Civita connection',
'Geometry.Connection.Smoothness': 'Smooth time-dependent connection families',
'Geometry.Flow.RicciFlow.Solution.Defs': 'Ricci-flow candidates and their tensor evolution equation',
'Geometry.Flow.RicciFlow.Solution.Basic': 'Ricci-flow solutions with canonical curvature',
'OpenGALib.Riemannian.VolumeVariation': 'Local metric-family regularity and total Riemannian volume',
'OpenGALib.Riemannian.Surface.Area': 'The area measure and total area of an immersed surface',
'OpenGALib.Interoperability.RicciFlow.ClosedSurfaceArea': 'The Ricci tensor traced on an immersed surface',
}

def source_url(module, lo, hi):
    upstream = module.startswith('DifferentialGeometry.')
    repo, rev = ('qinz1yang/differential-geometry', UPSTREAM_REVISION) if upstream else ('MathNetwork/OpenGA', SOURCE_REVISION)
    return f'https://github.com/{repo}/blob/{rev}/{module.replace(".", "/")}.lean#L{lo}-L{hi}'

PROOF_IDEAS = {
'hasDerivAt_area': 'Apply local-in-time total-volume variation to the metric induced on the compact surface by the fixed immersion. The Ricci-flow equation identifies its metric variation trace with minus twice the tangential Ricci trace, cancelling the factor one half in volume variation. The area and measure are those of the induced metric.',
'inducedMetric_regularOn': 'Express each induced Gram entry as the ambient metric evaluated on the differential of two surface chart vectors. Smoothness of the ambient family and the fixed immersion supplies its time derivative and joint continuity on the regular time set.',
'traceTimeDeriv_inducedMetric': 'Differentiate the induced Gram entries with the immersion fixed. The Ricci-flow equation gives minus twice the pulled-back Ricci entries. Contract with the inverse induced Gram matrix and take the trace.',
'hasDerivAt_totalRiemannianVolume': 'Choose a smooth time localization that agrees with the identity near the selected time and stays inside its regularity neighborhood. Apply global metric-family volume variation with constant integrand one, then use local equality of the original and localized volume functions.',
'comp': 'Compose the Gram entries with the smooth time map and apply the chain rule. Its image stays inside the regularity set, so the original derivative and continuity hypotheses apply.',
'volume_variation_formula': 'Differentiate each partition-weighted chart integral, and assemble the resulting derivatives using the finite partition of unity. Regularity also gives continuity of the global derivative density.',
'per_chart_hasDerivAt': 'Pull the weighted chart integral back to the model space. Compact support of the partition function and joint regularity give an integrable local derivative bound. Differentiate under the integral and return to the chart measure.',
'hasDerivAt_sqrt_det_eq_half_trace_inv_mul': 'Differentiate the finite determinant expansion and identify the derivative with the adjugate trace. Positive determinant permits replacing the adjugate by determinant times inverse and applying the square-root derivative formula.',
'hasDerivAt_det_of_entries': 'Differentiate the finite signed permutation expansion of the determinant. The product rule gives one term for each entry being differentiated.',
'perm_sum_eq_trace_adjugate_mul': 'Expand the adjugate using cofactors and the trace using its diagonal sum, then reindex the finite sums to match the differentiated determinant expansion.',
'trace_chartGramMatrix_inv_deriv_chart_independent': 'Transform the Gram matrix and its time derivative by the same time-independent basis change. Cancel the inverse transition matrices and use cyclic invariance of trace.',
'volume_variation_formula_of_chart_derivs': 'Differentiate the finite sum of partition-weighted chart integrals. The chart-sum identity identifies the sum of derivative terms with the global derivative integral.',
'volume_variation_formula_of_chart_integrals': 'The global integral agrees with the finite chart sum near the selected time. Differentiate that sum and substitute the assumed equality of its derivatives with the proposed value.',
'FunctionRegularAt_const': 'A constant integrand is continuous and has zero time derivative. These identities supply every field of the regularity structure.',
'of_chartGram_timeDeriv': 'Choose the supplied entry derivative fields. Uniqueness of derivatives identifies them with the derivative expressions in the regularity structure; the given joint continuity fills the remaining fields.',
'hasDerivAt_setIntegral_model': 'Apply dominated differentiation to model Haar measure restricted to the target set, retaining the stated measurability, integrability, neighborhood and pointwise derivative assumptions.',
}

CORE_DEFINITIONS = {
'OpenGALib.Riemannian.Surface.Area': r'For a fixed smooth immersion $f:N\to(M,g)$ of a Hausdorff smooth surface, define the area measure as the Riemannian volume measure of $h=f^*g$, and the total area by $$\operatorname{Area}_g(f)=\mu_h(N).$$ The Lean real-valued area uses the real conversion of the extended measure; finiteness on compact domains is proved. This measures area on the immersed domain, counting multiplicity.',
'OpenGALib.Interoperability.RicciFlow.ClosedSurfaceArea': r'Evaluate the ambient Ricci tensor on the differential images of the surface chart vectors to obtain a matrix $R_f$. If $H$ is the induced metric Gram matrix, define $$\operatorname{RicTrace}_f=\operatorname{tr}(H^{-1}R_f).$$ These are the concrete Ricci matrix and trace in the surface area derivative.',
'OpenGALib.Riemannian.VolumeVariation': 'The local regularity structure records joint continuity and time differentiability of chart Gram entries on a specified time set. Total Riemannian volume is the real-valued total mass of the actual volume measure. The included localization helpers support variation at a time with a regular neighborhood.',
'Analysis.Integration.Measure.ChartDensity': r'For a smooth metric with chart Gram matrix $G_\alpha$, define $$J_\alpha=\sqrt{\det G_\alpha}.$$ Weight model Haar measure on the extended chart target by this density and push it forward under the inverse chart to obtain the chart-local Riemannian measure.',
'Analysis.Integration.Measure.FamilyDefs': r'This bundle defines metric Gram families, chart density families, Riemannian measure families and $$\operatorname{tr}_{g_t}\dot g_t=\operatorname{tr}(G(t)^{-1}\dot G(t)).$$ Its regularity structures retain the source hypotheses on time derivatives and joint continuity over their full chart-time domains.',
'Geometry.Flow.RicciFlow.Solution.Basic': r'The solution structures combine a smooth time-dependent metric and connection, Levi-Civita compatibility, regularity of canonical curvature and the equation $$\partial_tg=-2\operatorname{Ric}(g).$$ Ricci is constructed from connection curvature. These structures define a solution; they do not prove existence of Ricci flow.',
}

def main():
    destination = DIRECTORY / 'publication.json'
    if destination.exists():
        prior = json.loads(destination.read_text())
        if prior['status'] != 'PREPARED' or any('publication' in r or 'submission' in r for r in prior['definitions'] + prior['theorems']):
            raise RuntimeError('Preserve the submitted publication ledger; do not regenerate it')
    e = Export()
    plan = json.loads((DIRECTORY / 'Metadata/export_plan.json').read_text())
    tags = ['closed-surface-area-variation', 'ricci-flow', 'riemannian-geometry', 'colding-minicozzi']
    definitions = []
    for row in plan['definition_bundles']:
        module = row['module']
        title = DEFINITION_TITLES[module.removeprefix('DifferentialGeometry.')]
        names = sorted({r['userName'] for k in row['groups'] for r in e.groups[k]['rows']
                        if r['kind'] in ('def', 'inductive') and not r['isPrivate'] and not r['isInstance']
                        and e.groups[k]['fact']['nameText'] and r['userName'].endswith(e.groups[k]['fact']['nameText'])})
        body = (DIRECTORY / row['path']).read_text()
        identifier = Path(row['path']).stem.removeprefix('Def_')
        lo = min(e.groups[k]['fact']['declStart']['line'] for k in row['groups'])
        hi = max(e.groups[k]['fact']['declEnd']['line'] for k in row['groups'])
        attribution = 'DifferentialGeometry' if module.startswith('DifferentialGeometry.') else 'OpenGA'
        statement = CORE_DEFINITIONS.get(module.removeprefix('DifferentialGeometry.'), title + '.') + ' '
        if names:
            statement += 'The principal declarations are ' + ', '.join('`' + n + '`' for n in names) + '. '
        statement += ('This bundle preserves the definitions and the proved construction helpers from the linked ' + attribution +
                      ' source needed by the closed-surface area-variation proof. All hypotheses and bundle instances are retained; '
                      'private helper names are made unique for cross-module imports. The original project is distributed under Apache-2.0. '
                      'The bundle supplies geometric or analytic infrastructure and does not by itself assert finite-time extinction.')
        payload = {'definition_name': identifier, 'definition_title': title, 'definition': body,
                   'natural_language_statement': statement, 'env': ENVIRONMENT, 'tags': tags,
                   'source': source_url(module, lo, hi)}
        deps = [line.removeprefix('import Definitions.Def_') for line in body.splitlines()
                if line.startswith('import Definitions.Def_ClosedSurface_')]
        definitions.append({'id': identifier, 'path': row['path'], 'sha256': digest(body.encode()),
                            'definitions': deps, 'payload': payload})
    theorems = []
    for row in plan['theorem_files']:
        name = row['name']
        title, statement = STATEMENTS[name.removeprefix(MEASURE)]
        g = e.groups[row['key']]
        f = g['fact']
        statement = statement.replace("\\'", "'")
        if name.startswith(MEASURE):
            statement += '\n\nProof from DifferentialGeometry, preserved and packaged by OpenGA with source attribution.'
        payload = {'theorem_name': name, 'theorem_title': title, 'preamble': row['preamble'],
                   'formal_statement': row['formal_statement'], 'natural_language_statement': statement,
                   'env': ENVIRONMENT, 'tags': tags,
                   'source': source_url(g['module'], f['declStart']['line'], f['declEnd']['line'])}
        body = (DIRECTORY / row['path']).read_bytes()
        proof = (DIRECTORY / row['proof_path']).read_bytes()
        deps = sorted({line.removeprefix('import Definitions.Def_') for line in (row['preamble'] + '\n' + proof.decode()).splitlines()
                       if line.startswith('import Definitions.Def_ClosedSurface_')})
        theorems.append({'id': name, 'path': row['path'], 'proof_path': row['proof_path'],
                         'sha256': digest(body), 'proof_sha256': digest(proof), 'definitions': deps,
                         'imports': row['children'], 'payload': payload,
                         'explanation': statement + '\n\n' + PROOF_IDEAS.get(name.split('.')[-1],
                           'The proof uses the definitions and helper identities from the cited source. '
                           + ('Its separate proved prerequisites are: ' + '; '.join(STATEMENTS[n.removeprefix(MEASURE)][0] for n in row['children']) + '. '
                              if row['children'] else '')
                           + 'The full source argument is retained, with its original hypotheses and source attribution.')})
    source_paths = [path_for(m) for m in e.modules]
    source_paths += list((DIRECTORY / 'Tools').glob('*.py')) + list((DIRECTORY / 'Tools').glob('*.lean'))
    record = {'schema_version': 1, 'batch': 'closed_surface_area_variation', 'status': 'PREPARED',
              'mission_id': '29133a9f-c412-4f19-968e-3deae9a335b5',
              'milestone_id': '33045187-e820-4325-a253-c8ba2c778897',
              'source_reviewed': True, 'source_revision': SOURCE_REVISION, 'upstream_revision': UPSTREAM_REVISION,
              'mathlib_rev': ENVIRONMENT, 'toolchain': 'leanprover/lean4:v4.33.1',
              'scope': 'Actual area variation for a fixed smooth immersion of a compact boundaryless surface under a smooth Ricci flow. No branch points or minimality claim.',
              'sources': [{'path': str(p.relative_to(REPOSITORY)), 'sha256': digest(p.read_bytes())} for p in source_paths],
              'transformations': {'private_and_instance_names': e.renames, 'method': 'Lean dependency and source-span oracles; source declaration subtraction; preserved proof bodies.'},
              'prerequisites': [{'theorem_id': '9f78021b-c594-4538-b61f-06a8831433af', 'path': 'Definitions/Def_DifferentialGeometry_SmoothRiemannianMetric.lean'},
                                {'theorem_id': '71d6823a-2014-4ec2-8a21-0f6e3cdb3232', 'path': 'Definitions/Def_OpenGA_ImmersedMetric.lean'}],
              'definitions': definitions, 'theorems': theorems, 'validation': {'status': 'pending'}}
    destination.write_text(json.dumps(record, indent=2, ensure_ascii=False) + '\n')
    print(f'Prepared {len(definitions)} definition bundles and {len(theorems)} theorem payloads; validation remains required.')

if __name__ == '__main__':
    main()
