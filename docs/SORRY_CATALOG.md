# Sorry Catalog

Central registry of `sorry` occurrences in OpenGALib. Every sorry carries a
classification and (for PRE-PAPER) a closure path. CI snapshots the total
count; new sorry additions require updating this file.

## Scope

This catalog covers the **public library content**: `Algebraic`, `Tensor`,
`Riemannian`, `GeometricMeasureTheory`. `Regularity/` is gitignored
(paper-specific consumer) and tracked locally; its sorrys are not in the
public count.

## Classification

* **PRE-PAPER** — gap in Mathlib API or framework primitive; closure path is
  framework self-build or Mathlib upstream.
* **CITED-BLACK-BOX** — theorem quoted from a paper, body never proven in
  the framework. The named theorem is the value; the proof is delegated to
  the citation.

## Total counts

| Module | PRE-PAPER | CITED-BLACK-BOX | Total |
|--------|-----------|------------------|-------|
| Algebraic | 5 | 0 | 5 |
| Tensor | 9 | 0 | 9 |
| Riemannian | 5 | 0 | 5 |
| GeometricMeasureTheory | 5 | 10 | 15 |
| **Total** | **24** | **10** | **34** |

CI workflow `.github/workflows/ci.yml` asserts the total equals 34 (`EXPECTED=34`).

## Algebraic (5)

| File:line | Identifier | Classification | Notes |
|-----------|-----------|---------------|-------|
| `Auxiliary/Fin.lean:86` | `addCases_succAbove_castAdd` | PRE-PAPER | Mathlib gap on `Fin.addCases` ∘ `Fin.succAbove` interaction. Mechanical case split. |
| `Auxiliary/Fin.lean:98` | `addCases_succAbove_natAdd` | PRE-PAPER | Sister lemma to above. Same shape. |
| `Auxiliary/ShuffleDeriv.lean:284` | `derivShuffleEquivLeft` injectivity branch | PRE-PAPER | Internal case in shuffle-derivative bijection. Inherited from external lib port. |
| `Auxiliary/ShuffleDeriv.lean:300` | `derivShuffleEquivLeft` surjectivity (cardinality) | PRE-PAPER | Cardinality balance `(m+n+1)·C(m+n,m) = C(m+n+1,m+1)·(m+1)`. Inherited from external lib. |
| `Auxiliary/ShuffleDeriv.lean:312` | `derivShuffleEquivLeft_sign` | PRE-PAPER | Sign of canonical `Quotient.out'` representatives. Inherited from external lib. |

## Tensor (9)

| File:line | Identifier | Classification | Notes |
|-----------|-----------|---------------|-------|
| `Alternating/Wedge.lean:378` | `uncurryFin_wedge_productL_precompL` | PRE-PAPER | Algebraic identity matching LHS/RHS via `derivShuffleEquivLeft`. Closure path documented in proof body. |
| `Alternating/Wedge.lean:387` | `uncurryFin_wedge_productL_precompR` | PRE-PAPER | Sister identity with sign `(-1)^m`. |
| `Alternating/Wedge.lean:715` | `domDomCongr_finAddFlip_wedge_self` | PRE-PAPER | Depends on removed Mathlib lemma `Equiv.Perm.finAddFlip_equiv_eqFin`. Currently unused; revisit if needed. |
| `DifferentialForm/Basic.lean:194` | `ederiv_basis_expansion` | PRE-PAPER | Basis expansion of exterior derivative. Mechanical from `fderiv_basis`. |
| `DifferentialForm/Basic.lean:286` | `iprod_wedge` algebra | PRE-PAPER | Interior product / wedge product interaction; algebraic. |
| `DifferentialForm/Basic.lean:293` | `pullback.smooth` | PRE-PAPER | Smoothness of `ω ∘ fderiv f` composition. |
| `DifferentialForm/Basic.lean:323` | `pullback_ederiv` (differentiability gap) | PRE-PAPER | Inner gap in pullback-commutes-with-ederiv proof. |
| `DifferentialForm/Basic.lean:326` | `pullback_ederiv` (outer) | PRE-PAPER | Outer goal of same proof. |
| `Product/Pretrivialization.lean:281` | `tensorProductCoordChange_contMDiffOn` | PRE-PAPER | Bundle pretrivialization plumbing; Mathlib gap on tensor-product bundle smoothness. |

## Riemannian (5)

| File:line | Identifier | Classification | Notes |
|-----------|-----------|---------------|-------|
| `Curvature.lean:241` | `riemannCurvature_inner_self_zero` | PRE-PAPER | Skew-symmetry of $R(X,Y)$. Closure path: metric-compat 4× + Hessian-Lie identity (`mfderiv_iterate_sub_eq_mlieBracket_apply`). Proof body sketches it. |
| `Curvature.lean:256` | `ricci_symm` | PRE-PAPER | Symmetry of Ricci. Closure path: trace-via-orthonormal-basis + Bianchi I (closed) + diagonal-zero (above). |
| `Connection.lean:1387` | `koszulCovDeriv_const_smoothAt` | PRE-PAPER | Path-B cascade leftover. Closure: write `metricRiesz_section_smoothAt` against `Bundle.ContMDiffRiemannianMetric` API via chart-pullback unwrapping of the Riesz isomorphism. Self-build follow-up. |
| `Operators/Bochner.lean:96` | `leibniz_trace_reduction` (E) | PRE-PAPER | Bochner intermediate: $\tfrac12 \Delta_g \|\nabla f\|^2 = \langle \Delta_\nabla \nabla f, \nabla f\rangle + \|\nabla^2 f\|^2$. Closure path: metric-compat ×2 on $\langle \nabla f, \nabla f\rangle$ + trace via `stdOrthonormalBasis` + `connectionLaplacian_eq_sum_secondCovDerivAt`. Detailed plan in docstring. |
| `Operators/Bochner.lean:135` | `connectionLaplacian_grad_eq_grad_laplacian_add_ricci` (G) | PRE-PAPER | Bochner intermediate: $\langle \Delta_\nabla \nabla f, \nabla f\rangle = \langle \nabla f, \nabla(\Delta_g f)\rangle + \mathrm{Ric}(\nabla f, \nabla f)$. Closure path: D.2 (Ricci identity, closed) + B (Hessian symmetry, closed modulo gradient smoothness) + F (Ricci trace formula, closed) + grad duality. Detailed plan in docstring. |

## GeometricMeasureTheory (15)

| File:line | Identifier | Classification | Notes |
|-----------|-----------|---------------|-------|
| `Rectifiability.lean:85` | `isRectifiable_of_stationary_density_pos` | CITED-BLACK-BOX | Allard 1972 / Pitts 1981 rectifiability theorem. |
| `HasNormal.lean:128` | `tangentCone_unitNormal_exists` body | PRE-PAPER | Currently `Classical.choose` over trivial existence. Real repair: extract cone normal from chart-rescale weak limit. |
| `FinitePerimeter.lean:83` | perimeter measurability | PRE-PAPER | Mathlib BV-on-charted-manifold gap. |
| `FinitePerimeter.lean:135` | reduced-boundary trichotomy | PRE-PAPER | Density-based trichotomy (interior / boundary / exterior). |
| `Varifold.lean:114` | `density_nonneg` | PRE-PAPER | Direct from definition of density via mass. |
| `Varifold.lean:141` | support characterization | PRE-PAPER | Standard support-via-positive-mass-on-balls. |
| `Isoperimetric/SobolevPoincare.lean:156` | Sobolev–Poincaré inequality | CITED-BLACK-BOX | Maggi 2012 §13. |
| `Isoperimetric/Euclidean.lean:111` | Euclidean isoperimetric (eq form) | CITED-BLACK-BOX | Maggi 2012 §14. |
| `Isoperimetric/Euclidean.lean:135` | Euclidean isoperimetric (sharp constant) | CITED-BLACK-BOX | Maggi 2012 §14. |
| `Isoperimetric/ReducedBoundary.lean:113` | reduced boundary structure | CITED-BLACK-BOX | De Giorgi structure theorem; Maggi 2012 §15. |
| `Isoperimetric/ReducedBoundary.lean:152` | reduced boundary (variant) | CITED-BLACK-BOX | Maggi 2012 §15. |
| `Isoperimetric/BVFunction.lean:114` | BV approximation | CITED-BLACK-BOX | Maggi 2012 §10. |
| `Isoperimetric/Coarea.lean:73` | coarea formula | CITED-BLACK-BOX | Maggi 2012 §18. |
| `Isoperimetric/Coarea.lean:117` | coarea (variant) | CITED-BLACK-BOX | Maggi 2012 §18. |
| `Isoperimetric/Relative.lean:87` | relative isoperimetric | CITED-BLACK-BOX | Maggi 2012 §16. |

## Notes

* PRE-PAPER is **not permanent technical debt**: every PRE-PAPER entry has a
  concrete closure path (either Mathlib API to extend, or framework
  self-build to perform). The classification distinguishes "ready to close
  with focused work" from "deliberately delegated to a citation".
* CITED-BLACK-BOX entries are **stable by design**: the framework states a
  named theorem from the literature and uses it without re-proving the body.
  These are the seven Maggi 2012 / Allard 1972 references plus the Bochner
  identity.
* Updating this file: when adding a new `sorry`, append a row with
  classification + notes, and bump `EXPECTED` in `.github/workflows/ci.yml`.
  When closing a sorry (replacing with a real proof), remove its row and
  decrement `EXPECTED`. The per-module sub-table count must equal the
  summary table count.
