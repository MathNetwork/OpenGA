# Sorry Catalog

Central registry of `sorry` occurrences in OpenGALib. Every sorry carries a
classification and (for PRE-PAPER) a closure path. CI snapshots the total
count; new sorry additions require updating this file.

## Scope

This catalog covers `Algebraic`, `Tensor`, `MetricGeometry`, `Riemannian`, `Bridges`,
`Comparison`, and `GeometricMeasureTheory`.

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
| MetricGeometry | 0 | 0 | 0 |
| Riemannian | 5 | 0 | 5 |
| Bridges | 1 | 0 | 1 |
| Comparison | 1 | 0 | 1 |
| GeometricMeasureTheory | 5 | 10 | 15 |
| **Total** | **26** | **10** | **36** |

CI workflow `.github/workflows/ci.yml` asserts the total equals 36
(`EXPECTED=36`).

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

## Riemannian (4)

| File:line | Identifier | Classification | Notes |
|-----------|-----------|---------------|-------|
| `Connection.lean:956` | `bianchi_second` | PRE-PAPER | Differential Bianchi identity $(\nabla_X R)(Y,Z) W + \text{cyclic} = 0$. Statement-only commit (`a08f02a`). Repair plan (in docstring): expand `riemannCurvature_commutator_form`, distribute `covDeriv_sub_field` to 12 cov-deriv-of-cov-deriv terms, group into 6 pairs via torsion-freeness, close via `bianchi_first` + `SmoothVectorField.mlieBracket_jacobi`. Infrastructure in place; estimated 80-120 LOC. |
| `Volume/ChartPullback.lean:75` | `volumeMeasure` | PRE-PAPER | Riemannian volume measure `vol_g`. Phase 1 skeleton of `riemannian-volume` branch — chart-pullback construction with partition-of-unity glue. Repair plan in docstring: (1) chart-wise pushforward of `√det(g_ij)·Lebesgue`, (2) chart-invariance via `g' = Jᵀ·g·J ⟹ √det g'  = \|det J\|·√det g` cancelling Lebesgue Jacobian, (3) global glue via Mathlib `Mathlib.Geometry.Manifold.PartitionOfUnity`. Estimated 150-250 LOC. |
| `Volume/ChartPullback.lean:89` | `instIsLocallyFiniteMeasure_volumeMeasure` | PRE-PAPER | `vol_g` locally finite. Repair plan: take chart-relative compact neighborhood, apply chart-pullback formula, bound `√det` by sup. ~30 LOC. |
| `Volume/ChartPullback.lean:98` | `instSigmaFinite_volumeMeasure` | PRE-PAPER | `vol_g` sigma-finite. Repair plan: `IsLocallyFiniteMeasure + SigmaCompactSpace ⟹ SigmaFinite` (standard Mathlib lemma). ~5 LOC. |
| `Volume/VolumeForm.lean:46` | `volumeFormAt` | PRE-PAPER | Pointwise volume form `dV_g(x) : Λⁿ(T_xM)*`. Phase 2 skeleton. Repair plan: Gram-matrix determinant `√det(g_ij(x))` extended by n-linear-alternating universal property; chart-invariance via `g' = Jᵀ·g·J`. Bridge `volumeMeasure_eq_integral_volumeForm` deferred until form-integration API lands. Estimated 80-120 LOC. |

The Bochner stack (closed via commit `de19ee7`) remains unconditional;
this is a *new* statement-only addition. Closure path documented above.

## Bridges (1)

| File:line | Identifier | Classification | Notes |
|-----------|-----------|---------------|-------|
| `RiemannianToLength.lean:101` | `IsRiemannianManifold.toLengthSpace` (`≤` direction) | PRE-PAPER | The bound `pathLength γ_continuous ≤ Manifold.pathELength I γ_smooth 0 1` for the `Path` constructed from a Mathlib smooth `γ : ℝ → M`. Closure path: partition-telescoping via `IsRiemannianManifold.out`, `Manifold.riemannianEDist_le_pathELength`, `Manifold.pathELength_add`, `Manifold.pathELength_mono` (~60–100 LOC). Repair trigger: first downstream consumer that destructures the `iInf` equation. See module docstring for the full repair plan. |

## Comparison (1)

| File:line | Identifier | Classification | Notes |
|-----------|-----------|---------------|-------|
| `BishopGromov/VolumeComparison.lean:39` | `bishopGromov_volume_comparison` | PRE-PAPER | **North-star.** Headline Bishop–Gromov volume comparison theorem (do Carmo Ch.10 §2 Thm 2.2 / Petersen Ch.9 Thm 27). Statement landed as the multi-stage driver of OpenGA Layer 1+3a+3b development. Closure path (sketched in the theorem docstring): Riccati comparison → Laplacian comparison → polar-coordinates volume comparison; each step needs Layer 3a infrastructure (smooth radial distance on `M ∖ Cut(p)`, Hessian comparison, polar-coordinates change-of-variables on Riemannian manifolds) that is not yet present. Sibling files in `Comparison/BishopGromov/` will host the chain. The proof, once landed, will also close the `Bridges/RiemannianToLength` `≤` sorry as a side effect. |

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
