# Sorry Catalog

Central registry of `sorry` occurrences in OpenGA. Every sorry carries a
classification + repair plan. CI snapshots the count; new sorry additions
require updating this file.

## Classification

* **PRE-PAPER** — gap in Mathlib API or framework primitive; closure path
  is framework self-build or Mathlib upstream.
* **CITED-BLACK-BOX** — theorem quoted from a paper, body never proven in
  the framework.
* **PAPER-INTERNAL** — proof obligation owned by an application paper, not
  the library.
* **CONJECTURAL** — open mathematics.

## Total counts

| Module | PRE-PAPER | CITED-BLACK-BOX | PAPER-INTERNAL | CONJECTURAL | Total |
|--------|-----------|------------------|----------------|-------------|-------|
| Riemannian | 4 | 0 | 0 | 0 | 4 |
| GeometricMeasureTheory | 5 | 9 | 0 | 0 | 14 |
| MinMax | 3 | 9 | 0 | 0 | 12 |
| Regularity | 0 | 2 | 0 | 0 | 2 |
| **Total** | **12** | **20** | **0** | **0** | **34** |

## Riemannian (4)

| File:line | Identifier | Classification | Repair plan |
|-----------|-----------|---------------|-------------|
| `Foundations/HessianLie.lean:309` | `mfderiv_iterate_sub_eq_mlieBracket_apply` | PRE-PAPER | Manifold scalar Hessian-Lie identity. Helpers #1 (`mfderiv_extChartAt_eq_id_eventually`) + #2 (`mfderiv_chart_compose_apply`) closed. Inner & outer locality bridges + base-point identities closed inline. Remaining: invoke Helper #2 on outer mfderivs + apply `flat_hessianLieWithin_apply` + `mlieBracketWithin_apply` for RHS bridge. ~30-50 additional lines. |
| `Curvature.lean:76` | `ricciTraceMap.map_add'` | PRE-PAPER | C^∞-linearity of Ricci trace map in first argument. Derive from `koszulCovDeriv` linearity in `X` (now that `koszulLeviCivita_exists` is closed, the route via `leviCivitaConnection`'s tensoriality is unblocked). |
| `Curvature.lean:77` | `ricciTraceMap.map_smul'` | PRE-PAPER | Same as above. |
| `Curvature.lean:112` | `ricci_symm` | PRE-PAPER | Symmetry of Ricci. Closure path: `riemannCurvature_inner_diagonal_zero` (skew-symm of R as endomorphism) via metric-compat applied 2×, scalar Hessian-Lie (above), → trace = 0; combined with Bianchi I + first-arg antisymmetry to derive `ricci(X,Y) - ricci(Y,X) = -tr(R(X,Y) endo) = 0`. Blocked by `mfderiv_iterate_sub_eq_mlieBracket_apply`. |

## GeometricMeasureTheory (14)

| File:line | Identifier | Classification | Repair plan |
|-----------|-----------|---------------|-------------|
| `Rectifiability.lean:85` | rectifiability of stationary varifolds | CITED-BLACK-BOX | Allard 1972 / Pitts 1981 rectifiability theorem; depends on `density > 0` assumption. |
| `HasNormal.lean:126` | `tangentCone_unitNormal_exists` body | PRE-PAPER | Currently uses `Classical.choose` over the trivial existence `⟨fun _ => 0, trivial⟩`. Real repair: extract cone normal from chart-rescale weak limit. |
| `FinitePerimeter.lean:83` | (perimeter measurability) | PRE-PAPER | Mathlib BV-on-charted-manifold gap. |
| `FinitePerimeter.lean:133` | `rbdy ⊆ topClosure` | PRE-PAPER | Reduced boundary topological inclusion; standard but mechanical. |
| `FinitePerimeter.lean:139` | reduced-boundary trichotomy | PRE-PAPER | Density-based trichotomy (interior / boundary / exterior). |
| `Varifold.lean:86` | `density_nonneg` | PRE-PAPER | Direct from definition of density via mass; Mathlib measure-theory lemmas. |
| `Varifold.lean:113` | support characterization | PRE-PAPER | Standard support-via-positive-mass-on-balls; Mathlib `MeasureTheory.Measure.support` adaptation. |
| `Isoperimetric/SobolevPoincare.lean:156` | Sobolev–Poincaré inequality | CITED-BLACK-BOX | Maggi 2012 §13. |
| `Isoperimetric/Euclidean.lean:111` | Euclidean isoperimetric | CITED-BLACK-BOX | Maggi 2012 §14. |
| `Isoperimetric/Euclidean.lean:135` | (variant) | CITED-BLACK-BOX | Same source. |
| `Isoperimetric/ReducedBoundary.lean:113` | reduced boundary structure | CITED-BLACK-BOX | De Giorgi structure theorem; Maggi 2012 §15. |
| `Isoperimetric/ReducedBoundary.lean:152` | (variant) | CITED-BLACK-BOX | Same source. |
| `Isoperimetric/BVFunction.lean:114` | BV property | CITED-BLACK-BOX | Maggi 2012 §10. |
| `Isoperimetric/Coarea.lean:73` | coarea formula | CITED-BLACK-BOX | Maggi 2012 §18. |
| `Isoperimetric/Coarea.lean:117` | (variant) | CITED-BLACK-BOX | Same source. |
| `Isoperimetric/Relative.lean:87` | relative isoperimetric | CITED-BLACK-BOX | Maggi 2012 §16. |

## MinMax (12)

| File:line | Identifier | Classification | Repair plan |
|-----------|-----------|---------------|-------------|
| `Sweepout/PullTight.lean:56` | `isStationary_of_minmaxLimit` | CITED-BLACK-BOX | Pull-tight lemma; Colding–De Lellis 2003 / Pitts 1981. |
| `Sweepout/MassCancellation.lean:56` | `perim_slice_le_width` | PRE-PAPER | Definitional inequality from `width` definition. |
| `Sweepout/Interpolation.lean:62` | interpolation lemma | CITED-BLACK-BOX | Standard min-max interpolation. |
| `Sweepout/MinMaxLimit.lean:144` | slices L¹ convergence | CITED-BLACK-BOX | Min-max limit characterization. |
| `Sweepout/MinMaxLimit.lean:151` | DChi weak convergence | CITED-BLACK-BOX | Same source. |
| `Sweepout/MinMaxLimit.lean:184` | (existence variant) | CITED-BLACK-BOX | Min-max sequence existence. |
| `Sweepout/MinMaxLimit.lean:197` | support characterization | CITED-BLACK-BOX | Standard support-from-limit. |
| `Sweepout/HomotopicMinimization.lean:122` | inner homotopic minimizer | CITED-BLACK-BOX | DLT 2013. |
| `Sweepout/HomotopicMinimization.lean:127` | outer homotopic minimizer | CITED-BLACK-BOX | DLT 2013. |
| `Sweepout/HomotopicMinimization.lean:184` | finiteness | CITED-BLACK-BOX | DLT 2013. |
| `Sweepout/NonExcessive.lean:83` | critical iff left/right critical | PRE-PAPER | Definitional, mechanical. |
| `Sweepout/NonExcessive.lean:251` | non-excessive ONVP existence | PRE-PAPER | Construction over generic compact manifold. |

## Regularity (2)

| File:line | Identifier | Classification | Repair plan |
|-----------|-----------|---------------|-------------|
| `SmoothRegularity.lean:124` | Hausdorff small singular set | CITED-BLACK-BOX | Wickramasekera 2014 main theorem. |
| `SmoothRegularity.lean:140` | smooth minimal hypersurface | CITED-BLACK-BOX | Wickramasekera 2014 + 2 ≤ n ≤ 6 specialization. |

## Notes

* This catalog tracks **public-facing** sorries (Riemannian /
  GeometricMeasureTheory / MinMax / Regularity packages). Application
  papers (e.g., AltRegularity) maintain their own catalogs.
* PRE-PAPER classification is **not permanent technical debt**: every
  PRE-PAPER entry has a concrete repair trigger (Mathlib API maturation
  or framework self-build follow-up).
* Updating this file: when adding a new `sorry`, add a row +
  classification + repair plan. When closing a sorry (replacing with a
  real proof), remove its row. CI checks total count matches §"Total
  counts" table.
