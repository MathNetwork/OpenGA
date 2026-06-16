# SmoothManifoldsLee integration worklist

Source: branch `import/smooth-manifolds-lee` (commit `a5f308c`, LehengChen,
2026-06-12) — a Lean 4 formalization of Lee's *Introduction to Smooth Manifolds*
Ch1–5, self-contained, Mathlib-only deps (v4.30.0), zero dependency on the
current OpenGALib.

This worklist is the output of the 2026-06-12 full overlap audit: 40+ parallel
agents classified each file against Mathlib (`.lake/packages/mathlib`) and
OpenGALib for duplication, rated it, and proposed a landing module. The audit
covers all 346 chapter files (339 batch-audited + 7 deep-subdirectory files
audited in a follow-up).

## Overall stats

| Dimension | Distribution |
|---|---|
| Overlap class | new 187 · mathlib-dup 95 · partial-dup 57 |
| Port value | high 52 · medium 101 · low 186 |
| Files with sorry | 106 |

About 28% of files substantially duplicate Mathlib (mostly textbook-numbered
wrappers / recall) and are skipped; the 187 new files are the porting body.

## Integration principles

1. **Port by target module, not chapter order.** The textbook layout
   (`ChapNN/SecNN_MM/`) does not enter the trunk; declarations are regrouped by
   mathematical object into domain modules.
2. **Declaration names mostly survive** (already Mathlib-style descriptive
   naming); namespaces follow our **domain-namespace convention** (namespace =
   directory name, cf. `Riemannian`/`Tensor`/`GeometricMeasureTheory`) — for the
   manifold domain that happens to be `namespace Manifold`, and sharing a root
   namespace with Mathlib is consistent with how we extend
   `TangentBundle`/`ContinuousLinearMap`, so **no new namespace is needed**. File
   structure is reorganized per `../../NAMING_CONVENTION.md`.
   - **Docstring house style (established merging #65):** anchor files (outside
     `Util/`) use single `**Math.**` tags only — the `AnchorPurity` linter
     forbids `**Eng.**`/`**Mixed.**`, so engineering detail is dropped or moved
     into `Util/`; module docstrings use architecture-layered narrative (not
     textbook order); provenance is demoted to a one-line `Provenance:` footer.
     Exemplar on develop: `OpenGALib/Manifold/Charts/CoordinateBall.lean`
     (db767b1). The earlier PLAN wording "Math./Eng. dual docstring" was a
     misread and is retired.
   - **defs still require lowerCamelCase** (`NAMING_CONVENTION.md` line 42): the
     staged source's snake_case (e.g. `curve_velocity`,
     `chart_coordinate_vectors_basis`) must be renamed when ported.
3. **Fold bundled classes into the existing system.** Classes like
   `TopologicalManifold n M` are just packaging of Mathlib instances (T2 +
   second-countable + `ChartedSpace`), the same design pattern as our existing
   `SmoothManifold M` (`Riemannian/Manifold/SmoothManifold.lean`). Port them into
   our packaging lineage rather than introducing a second set; whether to keep
   the explicit dimension (`n`) parameter is decided at fold-in time.
   - Overlap with OpenGALib: the audit found 0 `opengalib-dup` — our library sits
     directly on Mathlib's manifold machinery doing metric-layer-and-up content;
     the submanifold/immersion/coordinate-ball layer Lee covers, we lack entirely.
     The one interface contact point: `GeometricMeasureTheory/Varifold.lean`'s
     `LocalSmoothEmbeddingWitness` placeholder structure, which the embedded-
     submanifold theory should sit under and replace once ported.
4. **No sorry in the trunk.** Files with sorry either get proved first, or, if
   the statement layer itself contains sorry (e.g. Chap04's
   `rankAt`/`HasConstantRank`), the whole block is deferred.
5. **Normalize landing targets.** The per-agent `targetModule` suggestions below
   vary in path style (`Riemannian/Manifold/…`, `Riemannian/Submanifold/…`,
   etc.); in practice they converge into one top-level manifold domain
   (`OpenGALib/Manifold/`, established by #65), sitting below `Riemannian` and
   `GeometricMeasureTheory`.
6. Toolchain first: the staged code used Lean v4.30.0 stable, we were on rc2 —
   align before the first wave. (Resolved: both now on v4.30.0-rc2.)

## Shared abstraction layers

The two sides each implemented half of the same facilities (us:
metric/measure-facing; them: topology/embedding-facing). On merge the following
five layers become shared modules in the trunk, with each side's upper layers
importing them:

| Facility layer | OpenGALib has | Staged branch provides | Notes |
|---|---|---|---|
| Manifold bundled classes | `SmoothManifold M`, `RiemannianManifold M` | `TopologicalManifold n M`, `SmoothManifoldWithBoundary n M` | fold into one lineage; **boundary support is a gap of ours, and a prerequisite for the GMT divergence theorem** |
| Chart calculus | `Riemannian/Volume/Util/ChartOverlap.lean`, `ChartTransition.lean` | coordinate balls, centered charts, precompact coordinate balls, Euclidean slice coordinates | same-origin facilities, half each; should become a shared `Charts` module, moved out of `Volume/Util/` |
| Cutoff / partition of unity | `Riemannian/Manifold/BumpFunction.lean` | annular cutoff, partition-of-unity existence, exhaustion functions | both wrap the same batch of Mathlib primitives; merge into one smoothing module |
| Tangent-bundle localization | `Riemannian/TangentBundle/TangentSmooth.lean` (`trivAt` criterion) | tangent-bundle trivialization, point derivations, curve velocity | follows construction-order stop 4 |
| Submanifold abstraction | `Varifold.lean`'s `LocalSmoothEmbeddingWitness` (placeholder) | `IsEmbeddedSubmanifold` + slice-chart theory | follows construction-order stop 2; replaces the witness structure once ported |

Layers 1–3 are small, mostly sorry-free, and have consumers on both sides
already — good as the first merge batch, higher priority than chapter-ordered
porting.

## Construction ledger

Process: see `PLAN.md` (claim → update status, one branch per `port/` item,
quality gates, sign-off). Items are listed in dependency order; "parallel-OK"
items have no dependency between them.

| # | Item | Content | Deps | Status |
|---|---|---|---|---|
| 1 | `port/manifold-typeclass-core` | Layer 1: bundled-class lineage merge (`TopologicalManifold n M`, boundary-manifold class into the `SmoothManifold M` lineage; Chap01 Sec01/Sec01_06) | — | todo |
| 2 | `port/charts` | Layer 2: chart-calculus shared module (coordinate balls, centered charts + existing `ChartOverlap`/`ChartTransition` moved out and merged) | #1 | todo |
| 3 | `port/cutoffs` | Layer 3: cutoff / partition of unity / exhaustion into the `BumpFunction` system (Chap02 Sec02_10/11 high-value items) | #1 | todo (parallel with #2) |
| 4 | `port/embedded-submanifold` | Layer 5 upper half: `IsEmbeddedSubmanifold` + graph-style submanifold API (Chap05 Sec05_28) | #2 | todo |
| 5 | `port/slice-charts` | Layer 5 lower half: slice-theorem infrastructure (`Theorem_5_8/` family + Sec05_29) | #4 | todo |
| 6 | `port/submersion-covering` | submersion / immersion / covering maps (Chap04 Sec04_25/26 high-value cluster) | #2 | todo (parallel with #4–5) |
| 7 | `port/tangent-localization` | Layer 4: tangent-bundle localization (trivialization, point derivations, curve velocity; Chap03 high-value items) | #1 | todo (parallel with #2–6) |
| 8 | `port/varifold-witness-swap` | replace `LocalSmoothEmbeddingWitness` with the submanifold theory | #5 | todo |
| 9 | (on demand) medium items | see each chapter's "Consider" table | per item | backlog |

Prerequisite (not a work item): align toolchain to v4.30.0.

### Actual PR wave (2026-06-14, LehengChen)

LehengChen made his own finer-grained decomposition (a stacked PR chain, not a
strict match to the table above). Actual status takes precedence:

| PR | Branch | Content | Status |
|---|---|---|---|
| #65 | `port/coordinate-ball` | coordinate-ball chart predicates | **merged to develop** (docstrings house-style-revised in db767b1, serves as the exemplar) |
| #66 | `port/precompact-basis` | precompact coordinate-ball countable basis + locally-finite refinement | **merged to develop** (cherry-pick 498d57e, docstrings house-style-revised; second exemplar) |
| #67 | `port/charted-space-core` | manifold from a chart-family core | open, feedback posted |
| #68 | `port/exhaustion-cutoff` | exhaustion functions + local smoothness + partition-of-unity ⇒ paracompact | open, feedback posted |
| #69 | `port/curve-velocity-mfderiv` | curve velocity + mfderiv (has snake_case defs to rename) | open, feedback posted |
| #70 | `port/coordinate-components` | coordinate tangent components (has snake_case defs; inlines `tangent_coordinates_change`) | open, feedback posted |

Common feedback (pointing at merged #65 as the exemplar): ① docstring house
style (single Math tags / architecture narrative / provenance footer); ②
theorem Eng-lines must not narrate proofs; ③ snake_case defs → lowerCamelCase;
④ retarget base to develop now that #65 is merged.

## Follow-up audit: deep-subdirectory files (missed by the batch audit, now added)

| File | Main declarations | Class | Value | sorry | Rationale |
|------|----------|------|------|-------|------|
| Chap05/Sec05_29/Theorem_5_8/Common.lean | euclidean_slice_projection etc., 27 decls | new | high | no | Euclidean slice geometry and chart-centering infrastructure |
| Chap05/Sec05_29/Theorem_5_8/Index.lean | re-exports | new | medium | no | index file |
| Chap05/Sec05_29/Theorem_5_8/LocalNormalFormAPI.lean | rank_normal_form etc. | partial-dup | medium | no | wraps Mathlib immersion normal form, bridges Ch4 rank form |
| Chap05/Sec05_29/Theorem_5_8/LocalSliceAtlas.lean | slice_condition_chartAt etc., 30+ decls | new | high | no | core of the slice-condition atlas construction |
| Chap05/Sec05_29/Theorem_5_8/LocalSliceImmersion.lean | local_slice_condition_has_embedded_submanifold_structure etc., 11 decls | new | high | no | completion step for the embedded-submanifold structure on slices |
| Chap05/Sec05_36/Theorem_5_51/EuclideanHalfSlice.lean | euclidean_half_slice_projection_partial_homeomorph | new | medium | yes | half-slice boundary chart, half-finished |
| Chap05/Sec05_36/Theorem_5_51/Index.lean | re-exports | new | low | yes | downstream unimplemented |

---

# Chap01

## Port priority (high, 10 items)

| File | Declarations | Class | Target | sorry | Rationale |
|---|---|---|---|---|---|
| Sec01/Definition_1_extra_2.lean | IsCoordinateBall, centerAt, etc. | new | Manifold/Charts | no | Coordinate-ball/box-chart predicates, missing in Mathlib, foundation of the coordinate-ball stack |
| Sec01/Example_1_5.lean | RealProjectiveSpace, realProjectiveChart, etc. | new | Instances/ProjectiveSpace | no | RP^n quotient topology and standard affine charts, completely absent from Mathlib |
| Sec01/Example_1_8.lean | contDiffGroupoid_pi, instIsManifoldPi, etc. | new | Instances/Pi | no | Finite-product IsManifold instance, fills a gap Mathlib already flags |
| Sec01/Lemma_1_10.lean | isTopologicalBasis_isPrecompactCoordinateBall, etc. | new | Manifold/Charts | no | Countable basis of precompact coordinate balls, underpins partitions of unity / exhaustion sequences |
| Sec01_03/Definition_1_3_extra_1.lean | IsSmoothCoordinateBall, IsRegularCoordinateBall, etc. | new | Manifold/CoordinateBall | no | Smooth/regular coordinate-ball predicates, fully proved, needs decoupling from in-project dependencies |
| Sec01_04/Example_1_32.lean | regular_level_set_smooth_structure, etc. | new | Manifold/RegularLevelSet | no | Regular-level-set theorem, 1750 lines fully proved, Mathlib has no regular value theorem |
| Sec01_04/Lemma_1_35.lean | ChartedSpaceCore.toTopologicalSpace_t2Space, toChartedSpace_isManifold, etc. | new | Manifold/ChartedSpaceCore | no | T2/second-countable/smooth criteria for building a manifold from an atlas, missing in Mathlib |
| Sec01_06/Exercise_1_42.lean | IsRegularCoordinateHalfBall, etc. | new | Manifold/CoordinateBalls | yes | Countable basis of regular coordinate (half-)balls, all three theorems sorry |
| Sec01_07/Problem_1_9.lean | ComplexProjectiveSpace, complexProjectiveSpaceIsManifold, etc. | new | Instances/ComplexProjectiveSpace | no | Complete CP^n manifold structure with no sorry, host for Fubini-Study |
| Sec01_05/Proposition_1_40.lean | IsBoundaryModelCoordinateBall, countable_fundamentalGroup, etc. | partial-dup | Manifold/CoordinateBall | yes | Half-ball basis and countable fundamental group are the gaps, topological corollaries already in Mathlib, all sorry |

<details><summary>Consider (medium, 21 items)</summary>

| File | Declarations | Class | Target | sorry | Rationale |
|---|---|---|---|---|---|
| Sec01/Exercise_1_1.lean | HasCoordinateBallCharts, etc. | new | Manifold/Charts | no | Chart-shrinking/straightening lemmas complete, existential statements need restructuring |
| Sec01/Exercise_1_6.lean | realProjectiveSpace_t2Space, etc. | new | Instances/ProjectiveSpace | yes | Supplies the T2/second-countability needed by Example_1_5, all four sorry |
| Sec01/Exercise_1_7.lean | realProjectiveSpaceCompactSpace | new | Instances/ProjectiveSpace | no | RP^n compactness fully proved, best ported together with Example_1_5 |
| Sec01_03/Proposition_1_19.lean | exists_countable_regular_coordinate_ball_basis, etc. | new | Manifold/CoordinateBall | yes | Countable basis of regular coordinate balls is useful, proof has sorry and packaging needs restructuring |
| Sec01_04/Example_1_30.lean | graph_coordinate_chart, graph_charted_space, etc. | new | Manifold/GraphChart | yes | Graph chart space of a smooth map is the gap, key lemma sorry |
| Sec01_04/Example_1_33.lean | realProjectiveSpaceIsManifold, realProjectiveChartTransitionDiffeomorph, etc. | new | Instances/RealProjectiveSpace | no | ℝPⁿ smooth structure fully proved, requires porting upstream Example_1_5 first |
| Sec01_06/Definition_1_6_extra_1.lean | contMDiffOn_halfSpace_iff_forall_exists_smoothAmbientExtension, etc. | new | Manifold/HalfSpaceExtension | yes | Half-space ambient-extension smoothness criterion, key boundary lemma sorry |
| Sec01_06/Definition_1_6_extra_3.lean | IsSmoothCoordinateHalfBall, etc. | new | Manifold/CoordinateBalls | yes | Definition overlaps with Exercise_1_42, API must be merged first |
| Sec01_07/Problem_1_10.lean | problem_1_10_chart_matrix, block_column_subspace, etc. | new | GeometricMeasureTheory/Grassmannian/Charts | yes | Grassmann matrix coordinates can feed varifolds, main theorem all sorry |
| Sec01_07/Problem_1_11.lean | closed_unit_ball_smoothManifoldWithBoundary, etc. | new | SmoothManifold/ClosedBall | yes | Closed-ball manifold-with-boundary fills a gap, key theorem sorry, atlas taken from Problem_2_4 |
| Sec01_07/Problem_1_5.lean | sigmaCompactSpace_of_connected_paracompact_locallyCompact_t2, etc. | new | Manifold/Paracompactness | no | Paracompact⇒σ-compact converse and second-countability characterization, Mathlib only has the forward direction |
| Sec01_07/Problem_1_6.lean | supportedRadialTwistHomeomorph, exists_uncountably_many_distinct_smooth_structures, etc. | new | Manifold/SmoothStructures | no | Uncountably many smooth structures fully proved, mostly single-theorem scaffolding |
| Sec01/Definition_1_extra_1.lean | TopologicalManifold, dimension_eq, etc. | partial-dup | Manifold/TopologicalManifold | yes | C⁰-manifold packaging class, mostly wrappers and dimension invariance sorry |
| Sec01/Example_1_3.lean | graphMap, graph_coordinates, etc. | partial-dup | Manifold/Charts | no | Packaged homeomorphism graphOn≃ₜU missing in Mathlib, commonly used for GMT graph parametrization |
| Sec01/Theorem_1_15.lean | exists_countable_locallyFinite_refinement_of_isTopologicalBasis, etc. | partial-dup | Manifold/Charts | no | Countable locally-finite refinement of precompact coordinate balls, feeds partitions of unity |
| Sec01_02/Definition_1_2_extra_3.lean | IsSmoothAtlas, etc. | partial-dup | SmoothManifold/Atlas | no | Instance-free atlas predicate is new, niche scaffolding |
| Sec01_02/Proposition_1_17.lean | same_smooth_structure_iff_union_is_smooth_atlas, etc. | partial-dup | SmoothManifold/Atlas | no | Union criterion for same smooth structure is new, letI statement needs restructuring |
| Sec01_04/Example_1_36.lean | grassmannian, grassmannian.chart_equiv, etc. | partial-dup | Instances/Grassmannian | yes | Grassmann chart bijection is the gap, nontrivial lemma all sorry |
| Sec01_05/Proposition_1_38.lean | boundaryChart, boundaryTopologicalManifold, etc. | partial-dup | Manifold/InteriorBoundary | yes | Construction of the boundary as an (n-1)-manifold, nearly all sorry and bound to a proprietary model |
| Sec01_06/Exercise_1_44.lean | ModelWithCorners.interiorOpens, etc. | partial-dup | Manifold/InteriorBoundary | no | Small lemma that the interior is a boundaryless open submanifold, fills out boundary infrastructure |
| Sec01_06/Theorem_1_46.lean | isInteriorPoint_iff_of_mem_maximalAtlas, etc. | partial-dup | Manifold/InteriorBoundary | no | Boundary detection generalized to maximal-atlas charts, fully proved |

</details>

<details><summary>Skip (44 items — mostly Mathlib wrappers / recall files)</summary>

- Sec01/Definition_1_extra_3.lean — mathlib-dup — pure recall typeclass
- Sec01/Definition_1_extra_4.lean — mathlib-dup — recall plus thin wrapper
- Sec01/Example_1_4.lean — mathlib-dup — one-line re-wrap of the sphere instance
- Sec01/Example_1_9.lean — new — trivial abbrev
- Sec01/Exercise_1_14.lean — mathlib-dup — pure recall
- Sec01/Lemma_1_13.lean — mathlib-dup — duplicates Exercise_1_14
- Sec01/Proposition_1_11.lean — partial-dup — recall plus instance assembly
- Sec01/Proposition_1_12.lean — mathlib-dup — pure recall wrapper
- Sec01/Proposition_1_16.lean — new — one-line simpa citing 1.40
- Sec01/Theorem_1_2.lean — new — recall of an in-project sorry theorem
- Sec01_02/Definition_1_2_extra_1.lean — mathlib-dup — #check pointer
- Sec01_02/Definition_1_2_extra_2.lean — partial-dup — two-line wrapper
- Sec01_02/Definition_1_2_extra_4.lean — mathlib-dup — recall pointer
- Sec01_02/Definition_1_2_extra_5.lean — mathlib-dup — rfl-provable and sorry
- Sec01_02/Exercise_1_18.lean — mathlib-dup — zero-declaration pointer
- Sec01_02/Remark_1_2_extra_6.lean — mathlib-dup — recall pointer
- Sec01_03/Exercise_1_20.lean — new — restates 1.19 with no new declarations
- Sec01_03/Notation_1_3_extra_2.lean — mathlib-dup — extChartAt recall
- Sec01_04/Example_1_21.lean — partial-dup — thin assembly of a discrete manifold
- Sec01_04/Example_1_22.lean — mathlib-dup — sorry restatement of an instance
- Sec01_04/Example_1_23.lean — new — one-off counterexample with no API
- Sec01_04/Example_1_24.lean — mathlib-dup — thin combination / #check
- Sec01_04/Example_1_25.lean — mathlib-dup — one-line corollary plus #check
- Sec01_04/Example_1_26.lean — mathlib-dup — pure #check
- Sec01_04/Example_1_27.lean — mathlib-dup — #check plus sorry helper lemma
- Sec01_04/Example_1_28.lean — partial-dup — key openness sorry
- Sec01_04/Example_1_29.lean — mathlib-dup — two-step corollary
- Sec01_04/Example_1_31.lean — mathlib-dup — #check on the sphere instance
- Sec01_04/Example_1_34.lean — mathlib-dup — restatement of the product instance
- Sec01_04/Notation_1_4_extra_1.lean — mathlib-dup — notation cross-reference #check
- Sec01_05/Definition_1_5_extra_1.lean — partial-dup — clumsy packaging of the half-space model
- Sec01_05/Exercise_1_39.lean — mathlib-dup — zero-declaration #check
- Sec01_05/Exercise_1_41.lean — partial-dup — pure pointer file
- Sec01_05/Theorem_1_37.lean — mathlib-dup — single recall
- Sec01_06/Definition_1_6_extra_2.lean — mathlib-dup — class-style re-wrap of Mathlib
- Sec01_06/Exercise_1_43.lean — mathlib-dup — zero-declaration #check
- Sec01_06/Proposition_1_45.lean — mathlib-dup — pure recall
- Sec01_07/Problem_1_1.lean — new — line-with-two-origins counterexample with no API
- Sec01_07/Problem_1_12.lean — mathlib-dup — direct infer_instance call
- Sec01_07/Problem_1_2.lean — partial-dup — exercise-level thin combination
- Sec01_07/Problem_1_3.lean — mathlib-dup — bidirectional thin wrapper
- Sec01_07/Problem_1_4.lean — new — near-trivial lemma plus counterexample
- Sec01_07/Problem_1_7.lean — mathlib-dup — rebuilds the stereographic atlas, many sorry
- Sec01_07/Problem_1_8.lean — partial-dup — circle-specific exercise

</details>

## Summary

Chapter 1 audits 75 files in total; about sixty percent are recall, #check, or thin wrappers around existing Mathlib results and can be skipped outright. The assets genuinely worth porting cluster along two lines: first, the coordinate-ball / covering infrastructure (coordinate-ball predicates, countable basis of precompact coordinate balls, regular coordinate (half-)balls), which underpins partitions of unity, exhaustion sequences, and GMT covering arguments; second, instance-level gaps (complete manifold structures for RP^n and CP^n, the finite-product IsManifold instance, the regular-level-set theorem, the ChartedSpaceCore construction lemmas), all acknowledged Mathlib blanks and mostly sorry-free. Most medium-value entries are held back by residual sorry or in-project dependencies (the TopologicalManifold class, LeeBoundaryModelSpace) and require API restructuring and dependency resolution before porting.

---

---

# Chap02

## Port priority (high, 4 items)

| File | Declarations | Class | Target | sorry | Rationale |
|---|---|---|---|---|---|
| Sec02_12/Problem_2_4.lean | closed_unit_ball_fixed_atlas, split_at_coordinate, etc. | new | Instances/ClosedBall | no | Closed-ball manifold-with-boundary, 2600 lines sorry-free, directly supports the GMT divergence theorem |
| Sec02_11/Proposition_2_28.lean | exists_positive_smooth_exhaustion_function | new | Manifold/Exhaustion | no | Positive smooth exhaustion function fully proved, required by the noncompact L²/Bochner/GMT directions |
| Sec02_09/Example_2_14.lean | unitOpenBallDiffeomorph, smoothChartDiffeomorph, etc. | partial-dup | Manifold/Diffeomorph | no | Packages unit-ball≃ℝⁿ and chart diffeomorphisms; Mathlib only has scattered lemmas |
| Sec02_09/Proposition_2_15.lean | Diffeomorph.pi, Diffeomorph.restrictOpen, etc. | partial-dup | Manifold/Diffeomorph | yes | Product and open-submanifold restriction API is a gap; six auxiliary lemmas have sorry |

<details><summary>Consider (medium, 14 items)</summary>

| File | Declarations | Class | Target | sorry | Rationale |
|---|---|---|---|---|---|
| Sec02_09/Theorem_2_17.lean | Diffeomorph.dimension_eq, etc. | new | Manifold/Diffeomorph | no | Dimension invariance under diffeomorphism fully proved; Mathlib lacks this general lemma |
| Sec02_11/Definition_2_11_extra_2.lean | Function.IsSmoothOn, etc. | new | Manifold/SmoothExtension | no | Local-extension smoothness predicate over a subtype domain; needs alignment with ContMDiffOn |
| Sec02_11/Definition_2_11_extra_3.lean | Function.IsExhaustionFunction, etc. | new | Manifold/Exhaustion | no | Exhaustion-function class plus proper lemma; the API foundation for 2.28 |
| Sec02_11/Lemma_2_26.lean | exists_supported_contMDiffMap_extension_of_isClosed | new | Manifold/SmoothExtension | yes | Smooth extension from a closed set is a genuine gap; only the statement exists, proof needed from scratch |
| Sec02_12/Problem_2_10.lean | smooth_iff_pullback_preserves_smooth_real_functions, etc. | new | Manifold/SmoothFunctionCriterion | yes | Useful criterion: pullback preserves smooth functions; theorem entirely sorry |
| Sec02_12/Problem_2_11.lean | Projectivization.basisMap, BasisCompatible, etc. | new | Instances/Projectivization | yes | Projectivization structure-transport layer; key proofs sorry and depend on Chapter 1 |
| Sec02_12/Problem_2_13.lean | paracompactSpace_of_hasSubordinatePartitionOfUnity | new | Manifold/PartitionOfUnity | no | Partition of unity ⇒ paracompact (converse) fully proved; Mathlib only has the forward direction |
| Sec02_12/Problem_2_6.lean | projectivizationMap, contMDiff_projectivizationMap, etc. | new | Manifolds/ProjectiveSpace | no | Homogeneous map descending to ℝPⁿ is new; needs the projective atlas ported first |
| Sec02_12/Problem_2_7.lean | smooth_functions_not_finiteDimensional, etc. | new | Util/SmoothFunctionSpace | no | C^∞(M,ℝ) infinite-dimensional fully proved; fairly niche for this library's direction |
| Sec02_08/Corollary_2_8.lean | gluing_lemma_for_smooth_maps | partial-dup | Manifold/SmoothManifold | no | Smooth-sheaf gluing unpacked into a usable ContMDiff-level statement |
| Sec02_08/Exercise_2_2.lean | contMDiff_open_submanifold_halfspace_iff_forall_exists_smoothAmbientExtension, etc. | partial-dup | Manifold/Boundary | no | Half-space extension criterion is a genuine gap; needs accompanying Chapter 1 dependency files |
| Sec02_09/Theorem_2_18.lean | Diffeomorph.restrictInterior, etc. | partial-dup | Manifold/Diffeomorph | yes | Restriction to manifold interior is new; depends on in-project facilities, simp lemmas sorry |
| Sec02_11/Proposition_2_25.lean | exists_smooth_bump_function_for | partial-dup | Manifold/BumpFunction | no | Bump with strict tsupport⊆U closed set; can extend this library's module |
| Sec02_12/Problem_2_3.lean | hopf_map, hopf_map_smooth, etc. | partial-dup | Instances/HopfFibration | yes | Hopf map S³→S² is a new canonical example; five proofs entirely sorry |

</details>

<details><summary>Skip (40 items — mostly Mathlib wrappers / recall files)</summary>

- Sec02_08/Definition_2_8_extra_2.lean — mathlib-dup — pure #check restatement
- Sec02_08/Definition_2_8_extra_4.lean — mathlib-dup — thin pointwise corollary
- Sec02_08/Definition_2_8_extra_5.lean — mathlib-dup — recall numbering cross-reference
- Sec02_08/Definition_2_8_extra_6.lean — partial-dup — existing API already covers it
- Sec02_08/Exercise_2_1.lean — mathlib-dup — only #check of the ring structure
- Sec02_08/Exercise_2_11.lean — mathlib-dup — three recalls
- Sec02_08/Exercise_2_3.lean — mathlib-dup — two-line wrapper
- Sec02_08/Exercise_2_7.lean — mathlib-dup — pure recall cross-reference
- Sec02_08/Exercise_2_9.lean — mathlib-dup — four-line wrapper
- Sec02_08/Notation_2_8_extra_3.lean — mathlib-dup — notation cross-reference #check
- Sec02_08/Proposition_2_10.lean — mathlib-dup — four #checks
- Sec02_08/Proposition_2_4.lean — mathlib-dup — single #check
- Sec02_08/Proposition_2_5.lean — mathlib-dup — single #check
- Sec02_08/Proposition_2_6.lean — mathlib-dup — two #checks
- Sec02_08/Remark_2_8_extra_1.lean — new — terminology predicate with no mathematical content
- Sec02_08/Remark_2_8_extra_7.lean — mathlib-dup — zero-declaration vocabulary restatement
- Sec02_09/Definition_2_9_extra_1.lean — mathlib-dup — pure #check
- Sec02_09/Exercise_2_16.lean — partial-dup — recall scaffolding
- Sec02_09/Exercise_2_19.lean — partial-dup — recall scaffolding
- Sec02_10/Definition_2_10_extra_1.lean — mathlib-dup — docs plus a single #check
- Sec02_10/Definition_2_10_extra_2.lean — mathlib-dup — wrapper already in this library
- Sec02_10/Definition_2_10_extra_3.lean — mathlib-dup — definition recall
- Sec02_10/Definition_2_10_extra_4.lean — mathlib-dup — definition recall
- Sec02_10/Exercise_2_24.lean — mathlib-dup — #check specialization
- Sec02_10/Lemma_2_20.lean — mathlib-dup — recall pointer
- Sec02_10/Lemma_2_21.lean — partial-dup — smoothStep already covers it
- Sec02_10/Lemma_2_22.lean — partial-dup — ContDiffBump already provides it
- Sec02_10/Theorem_2_23.lean — mathlib-dup — sorry restatement
- Sec02_11/Definition_2_11_extra_1.lean — new — trivial constant-function check
- Sec02_11/Exercise_2_27.lean — new — pedagogical counterexample
- Sec02_11/Theorem_2_29.lean — mathlib-dup — six-line specialization wrapper
- Sec02_12/Problem_2_1.lean — new — pedagogical counterexample, no API
- Sec02_12/Problem_2_12.lean — new — single-sorry main theorem
- Sec02_12/Problem_2_14.lean — mathlib-dup — literal recall
- Sec02_12/Problem_2_5.lean — new — textbook-specific, contains two sorry
- Sec02_12/Problem_2_8.lean — new — depends on an unported atlas
- Sec02_12/Problem_2_9.lean — new — textbook-specific, heavy auxiliary machinery
- Sec02_12/Problem_2_9_corecheck.lean — new — pipeline snapshot
- Sec02_12/Problem_2_9_pre_north.lean — new — pipeline snapshot
- Sec02_12/Problem_2_9_prefixcheck.lean — new — pipeline snapshot

</details>

## Summary

Chapter 2 audited 55 files in total, most of which (about 40) are #check- or recall-style restatements of Mathlib's existing ContMDiff / smooth-function / partition-of-unity API and can be skipped outright. The core assets genuinely worth porting cluster along two lines: first, the Diffeomorph infrastructure (products, open-submanifold restriction, dimension invariance, the packaged unit-ball and chart diffeomorphisms); second, the closed-ball manifold-with-boundary construction (Problem 2.4, 2600 lines sorry-free) and the positive smooth exhaustion function (Proposition 2.28), the latter two directly supporting the gaps in the GMT divergence theorem and the noncompact L²/Bochner directions. The medium-value items mostly revolve around smooth extension, projective-space structure, and pullback criteria; some still contain sorry, and they are best introduced in dependency order once their target modules have taken shape.

---

---

# Chap03

## Port priority (high, 4 items)

| File | Declarations | Class | Target | sorry | Rationale |
|---|---|---|---|---|---|
| Sec03_14/Proposition_3_9.lean | mfderiv_open_subset_inclusion_isInvertible | new | Util/Tangent | no | Full proof that the differential of an open-subset inclusion is invertible; Mathlib lacks this tangent-space identification API |
| Sec03_17/Proposition_3_23.lean | exists_smooth_curve_with_velocity, exists_smooth_curve_with_velocity_boundaryless, etc. | new | CurveVelocity | no | Surjectivity of curve velocity onto the tangent space including the boundary case; entirely missing from Mathlib |
| Sec03_16/Proposition_3_20.lean | tangent_bundle_opens_trivializationAt_eq_toProd, globalChartDiffeomorph, etc. | partial-dup | TangentBundle/Trivialization | no | Full proof of single-chart tangent-bundle trivialization; the main def depends on 3.22 which contains sorry |
| Sec03_20/Problem_3_7.lean | TangentSpace.toPointDerivation, smooth_germ_derivation_existsUnique_tangentVector, etc. | partial-dup | TangentBundle/PointDerivation | yes | Equivalence tangent vector ≃ germ derivation; a well-known Mathlib gap, with two remaining sorrys |

<details><summary>Consider (medium, 11 items)</summary>

| File | Declarations | Class | Target | sorry | Rationale |
|---|---|---|---|---|---|
| Sec03_13/Proposition_3_2.lean | directional_point_derivation, geometric_to_point_derivation_linear_equiv, etc. | new | Util/Tangent/PointDerivation | yes | Geometric tangent vector ↔ derivation equivalence is a genuine gap, but Euclidean-only with the key step entirely sorry |
| Sec03_14/Lemma_3_11.lean | mfderiv_half_space_inclusion_isInvertible_of_boundary_eq_zero | new | Manifold/Boundary | yes | Differential of half-space inclusion at a boundary point is invertible; statement only, no proof to port |
| Sec03_14/Proposition_3_8.lean | PointDerivation.congr_of_eqOn_nhds | new | Manifold/Derivation | no | Complete bump-function proof of derivation locality, but this library does not use the derivation model |
| Sec03_17/Definition_3_17_extra_1.lean | curve_velocity, curve_velocityWithin, etc. | new | CurveVelocity | no | Thin wrapper naming curve velocity; the basis for porting 3.23 |
| Sec03_18/Definition_3_18_extra_3.lean | SmoothCurveAt, CurveVelocityClass, etc. | new | TangentBundle/CurveVelocity | yes | Curve velocity realizing the tangent space; two core theorems sorry, needs redesign |
| Sec03_18/Definition_3_18_extra_4.lean | IsCoordinateTangentVector, TangentSpace.coordinateComponent, etc. | new | TangentBundle/CoordinateComponents | no | Fully proved coordinate-component API; missing from Mathlib, pedagogically oriented |
| Sec03_20/Problem_3_4.lean | tangentBundle_circle_diffeomorph_prodLie, circleTangentFiberDiffeomorph, etc. | new | TangentBundle/LieGroupTrivialization | no | Full proof of Lie-group trivialization TG ≃ G × Lie(G); hardcoded circle needs generalization |
| Sec03_14/Proposition_3_6.lean | mfderiv_comp_of_smooth, diffeomorph_mfderiv_symm_eq_symm | partial-dup | Util/Tangent | no | Differential of a diffeomorphism's inverse equals the inverse of the differential; small glue missing from Mathlib |
| Sec03_15/Proposition_3_15.lean | chart_mdifferentiable_of_mem_maximalAtlas, chart_coordinate_vectors_basis | partial-dup | Util/Chart/CoordinateBasis | no | Packages chart mfderiv into a Basis; small reusable coordinate API |
| Sec03_16/Corollary_3_22.lean | tangentMap_diffeomorph, tangentMap_comp_of_smooth, etc. | partial-dup | TangentBundle/Diffeomorph | yes | Diffeomorph induces a tangent-bundle diffeomorphism; five auxiliary lemmas sorry |
| Sec03_20/Problem_3_1.lean | isLocallyConstant_of_mfderiv_eq_zero, mfderiv_eq_zero_iff_isLocallyConstant, etc. | partial-dup | TangentBundle/MFDerivLocallyConstant | yes | mfderiv ≡ 0 iff locally constant; the forward direction is sorry-blocked |

</details>

<details><summary>Skip (42 items — mostly Mathlib wrappers / recall files)</summary>

- Sec03_13/Corollary_3_3.lean — new — Euclidean-restricted, entirely sorry
- Sec03_13/Definition_3_13_extra_1.lean — mathlib-dup — thin wrapper plus notation
- Sec03_13/Definition_3_13_extra_2.lean — mathlib-dup — #check restatement only
- Sec03_13/Definition_3_13_extra_3.lean — mathlib-dup — rfl-level restatement
- Sec03_13/Exercise_3_5.lean — mathlib-dup — pure #check recall
- Sec03_13/Lemma_3_1.lean — mathlib-dup — one-line Euclidean corollary
- Sec03_13/Lemma_3_4.lean — mathlib-dup — one-line wrapper
- Sec03_14/Definition_3_14_extra_1.lean — mathlib-dup — restates the mfderiv signature
- Sec03_14/Definition_3_14_extra_2.lean — mathlib-dup — single #check
- Sec03_14/Exercise_3_7.lean — mathlib-dup — pure #check restatement
- Sec03_14/Proposition_3_10.lean — mathlib-dup — one-line defeq
- Sec03_14/Proposition_3_12.lean — mathlib-dup — sorry restatement of dimension
- Sec03_14/Proposition_3_13.lean — mathlib-dup — one-line wrapper with sorry
- Sec03_15/Definition_3_15_extra_1.lean — partial-dup — already covered by existing API
- Sec03_15/Definition_3_15_extra_2.lean — partial-dup — one-line .repr wrapper
- Sec03_15/Example_3_16.lean — new — textbook numerical example
- Sec03_15/Exercise_3_17.lean — new — pedagogy-only example
- Sec03_15/Remark_3_15_extra_3.lean — mathlib-dup — pure recall
- Sec03_15/Remark_3_15_extra_4.lean — partial-dup — two-line glue already present
- Sec03_15/Remark_3_15_extra_5.lean — mathlib-dup — recall restatement
- Sec03_16/Definition_3_16_extra_1.lean — mathlib-dup — recalls TangentBundle
- Sec03_16/Definition_3_16_extra_3.lean — mathlib-dup — #check only
- Sec03_16/Exercise_3_19.lean — new — single rfl theorem
- Sec03_16/Notation_3_16_extra_2.lean — mathlib-dup — notation plus #check only
- Sec03_16/Notation_3_16_extra_4.lean — mathlib-dup — recalls bridge lemma
- Sec03_16/Proposition_3_18.lean — mathlib-dup — specializes contMDiff_proj
- Sec03_16/Proposition_3_21.lean — mathlib-dup — single #check specialization
- Sec03_17/Proposition_3_24.lean — mathlib-dup — one-line evaluation of the chain rule
- Sec03_17/Corollary_3_25.lean — mathlib-dup — restates 3.24
- Sec03_18/Definition_3_18_extra_1.lean — mathlib-dup — notation plus one-line instance
- Sec03_18/Definition_3_18_extra_2.lean — partial-dup — trivial abbrev plus sorry
- Sec03_19/Definition_3_19_extra_1.lean — mathlib-dup — recalls Category
- Sec03_19/Definition_3_19_extra_2.lean — mathlib-dup — recalls IsIso
- Sec03_19/Definition_3_19_extra_3.lean — mathlib-dup — recalls the small-category concept
- Sec03_19/Definition_3_19_extra_4.lean — mathlib-dup — #check functor only
- Sec03_19/Definition_3_19_extra_5.lean — mathlib-dup — #check contravariant functor only
- Sec03_19/Example_3_26.lean — partial-dup — pedagogical example
- Sec03_19/Exercise_3_27.lean — mathlib-dup — recall, no new proof
- Sec03_20/Problem_3_3.lean — mathlib-dup — pure recall restatement
- Sec03_20/Problem_3_5.lean — new — textbook-only exercise
- Sec03_20/Problem_3_6.lean — new — concrete example, almost entirely sorry
- Sec03_20/Problem_3_8.lean — new — pure recall bridge file

</details>

## Summary

Chapter 3 audited 53 files in total, roughly three-quarters of which are Mathlib duplicates (recall/#check restatements or one-line wrappers) and can be skipped outright. The high-value items genuinely worth porting cluster around tangent-space infrastructure: invertibility of the differential of an open-subset inclusion (Proposition 3.9), surjectivity of curve velocity (Proposition 3.23), single-chart tangent-bundle trivialization (Proposition 3.20), and the tangent-vector–derivation equivalence (Problem 3.7); two of the first three are already entirely sorry-free. The medium-value items mostly revolve around the derivation model and the coordinate-basis API, but generally contain sorrys or need design rework, so it is advisable to follow up on them only after the high-value items have landed in the CurveVelocity and Tangent utility modules.

---

---

# Chap04

## Port priority (high, 16 items)

| File | Declarations | Class | Target | sorry | Rationale |
|---|---|---|---|---|---|
| Sec04_21/Exercise_4_3.lean | prod_fst_isSmoothSubmersion, prod_mk_right_isImmersion, etc. | new | Manifold/ImmersionSubmersion | no | Product-projection submersion / slice immersion fully proved, includes reusable chart groupoid infrastructure |
| Sec04_21/Exercise_4_4.lean | IsSmoothSubmersion.comp, IsImmersion.comp, etc. | new | Manifold/ImmersionSubmersion | yes | Submersion composition and rank API, tackles a Mathlib TODO, one helper lemma has 3 sorry |
| Sec04_22/Proposition_4_8.lean | IsLocalDiffeomorph.isImmersion, is_local_diffeomorph_iff_is_immersion_and_is_smooth_submersion, etc. | new | Manifold/Submersion | no | Local diffeomorphism ↔ immersion + submersion fully proved, upstream predicate has sorry |
| Sec04_22/Theorem_4_5.lean | isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible, model_partialDiffeomorph_of_inverse_function_theorem, etc. | new | Manifold/InverseFunctionTheorem | no | Manifold-version inverse function theorem fully proved, an explicit Mathlib TODO |
| Sec04_24/Exercise_4_16.lean | IsImmersion.ex416_comp, IsSmoothEmbedding.comp, etc. | new | SmoothManifold/Immersion | yes | Immersion / smooth-embedding composition, Mathlib proof_wanted, one remaining sorry |
| Sec04_25/Definition_4_25_extra_2.lean | Topology.IsTopologicalSubmersion, IsTopologicalSubmersion.isQuotientMap, etc. | new | Manifold/Submersion | no | Topological-submersion API fully proved (open / quotient maps), missing from Mathlib |
| Sec04_25/Proposition_4_28.lean | Manifold.IsSmoothSubmersion, IsSmoothSubmersion.isOpenMap, etc. | new | Manifold/Submersion | no | Defines the smooth-submersion structure Mathlib lacks, depends on 4.26 which has sorry |
| Sec04_25/Theorem_4_26.lean | Manifold.IsSmoothLocalSection, smooth_submersion_iff_exists_smooth_local_section_through_every_point, etc. | new | Manifold/Submersion | yes | Local-section theorem characterizing submersions, main-theorem sorry needs rank-theorem-level work |
| Sec04_25/Theorem_4_29.lean | Manifold.contMDiff_iff_comp_of_surjective_smooth_submersion | new | Manifold/Submersion | yes | Surjective-submersion characteristic property is the workhorse lemma for quotient manifolds, only the statement has sorry |
| Sec04_25/Theorem_4_30.lean | Manifold.existsUnique_contMDiff_lift_of_surjective_smooth_submersion | new | Manifold/Submersion | yes | Existence-uniqueness of smooth lifts for quotient manifolds, core infrastructure, proof is sorry |
| Sec04_26/Definition_4_26_extra_1.lean | Manifold.IsSmoothCoveringMap, IsUniversalSmoothCoveringMap, etc. | new | Manifold/CoveringMap | no | Core definition layer for smooth covering maps, Mathlib only has the topological version |
| Sec04_26/Exercise_4_37.lean | IsLocalDiffeomorph.isSmoothLocalSection, IsSmoothCoveringMap.isSmoothLocalSection, etc. | new | Manifold/CoveringMap | no | Continuous local sections are automatically smooth, fully proved general upgrade lemma |
| Sec04_26/Proposition_4_36.lean | IsCoveringMap.exists_localSectionOn, IsSmoothCoveringMap.localSection_eq, etc. | new | Manifold/CoveringMap | no | Existence of smooth local sections and uniqueness on preconnected sets, complete API |
| Sec04_26/Proposition_4_40.lean | exists_unique_smooth_covering_structure, lifted_covering_chartedSpace, etc. | new | Manifold/CoveringMap | no | Unique smooth structure on a topological cover, 700-line sorry-free major theorem |
| Sec04_26/Proposition_4_46.lean | isSmoothCoveringMap_of_proper_localDiffeomorph, fiber_finite_of_proper_local_diffeomorph, etc. | new | Manifold/CoveringMap | no | Proper local diffeomorphism ⇒ covering map criterion fully proved, port requires merging back into the formal definition |
| Sec04_27/Problem_4_5.lean | complexProjectiveQuotientMap_isSmoothSubmersion, complexProjectiveLine_diffeomorphic_sphere, etc. | new | Instances/ComplexProjectiveSpace | no | CP^n quotient submersion fully proved, includes the capstone CP^1 ≅ S^2 construction |

<details><summary>Consider (medium, 22 items)</summary>

| File | Declarations | Class | Target | sorry | Rationale |
|---|---|---|---|---|---|
| Sec04_21/Definition_4_21_extra_1.lean | rank_at_eq_finrank_range_mfderiv, is_immersion_iff_forall_injective_mfderiv, etc. | new | Manifold/Rank | yes | Rank API fills a Mathlib gap, but theorems are all sorry, only statements portable |
| Sec04_21/Proposition_4_1.lean | exists_open_restriction_isSmoothSubmersion_of_surjective_mfderiv, exists_open_restriction_isImmersion_of_injective_mfderiv | new | Manifold/ImmersionSubmersion | yes | Pointwise surjective/injective mfderiv gives a local submersion/immersion, proofs all sorry |
| Sec04_22/Exercise_4_10.lean | smooth_iff_comp_left_of_isLocalDiffeomorph, smooth_iff_comp_right_of_surjective_isLocalDiffeomorph | new | Manifold/LocalDiffeomorph | no | Detecting smoothness via pre/post composition with a local diffeomorphism, fully proved iff lemmas |
| Sec04_23/Theorem_4_14.lean | constant_rank_surjective_is_smooth_submersion, constant_rank_injective_is_immersion, etc. | new | Manifold/RankTheorem | yes | Global rank theorem is a genuine gap, but all three proofs are sorry, statements only |
| Sec04_23/Theorem_4_15.lean | boundary_immersion_normal_form, BoundaryLocalCoordinateNormalFormAt, etc. | new | Manifold/Boundary | yes | Boundary normal form for immersions of manifolds-with-boundary, GMT-relevant but main theorem sorry |
| Sec04_24/Definition_4_24_extra_2.lean | Topology.IsTopologicalImmersion, IsEmbedding.isTopologicalImmersion, etc. | new | SmoothManifold/Immersion | no | Small fully-proved topological API for the local-embedding predicate, limited standalone value |
| Sec04_24/Proposition_4_22.lean | smooth_embedding_of_injective_isImmersion_isOpenMap, smooth_embedding_of_compact_source_injective_isImmersion, etc. | new | SmoothManifold/Embedding | yes | Skeleton of sufficient conditions for an injective immersion to be an embedding, all five proofs sorry |
| Sec04_24/Theorem_4_25.lean | Manifold.isImmersion_iff_forall_exists_open_restriction_isSmoothEmbedding | new | SmoothManifold/Embedding | yes | Local-embedding theorem is a genuine gap, but only a single sorry stub |
| Sec04_25/Definition_4_25_extra_1.lean | ContinuousMap.IsLocalSection, Function.RightInverse.isLocalSection_restrict_top, etc. | new | Manifold/Submersion | no | Local-section predicate for continuous maps, small fully-proved foundation layer |
| Sec04_25/Theorem_4_31.lean | Manifold.existsUnique_diffeomorph_of_surjective_smooth_submersions_constant_on_each_others_fibers | new | Manifold/Submersion | yes | Uniqueness of smooth quotients, a corollary of 4.29/4.30, statement-only sorry |
| Sec04_26/Exercise_4_38.lean | Manifold.IsSmoothCoveringMap.pi, isCoveringMap_pi, etc. | new | Manifold/CoveringMap | no | Finite-product theorem for covering maps, no sorry, port needs streamlining the diffeomorphism pipeline first |
| Sec04_26/Exercise_4_39.lean | Bundle.Trivialization.sheet_coordinate_eq_on_component, component_bijOn_baseSet, etc. | new | Manifold/CoveringMap | no | Sheet-decomposition lemmas fully proved, Trivialization API missing from Mathlib, somewhat niche |
| Sec04_26/Proposition_4_33.lean | IsSmoothCoveringMap.isSmoothSubmersion, diffeomorphOfInjective, etc. | new | Manifold/CoveringMap | yes | Basic-property interface for covering maps is correct, but four of five are sorry |
| Sec04_27/Problem_4_11.lean | isProperMap_iff_finite_fibers_of_isCoveringMap, exists_smoothCoveringMap_not_isProperMap | new | MetricGeometry/Covering/ProperMap | yes | Cover-is-proper iff fibers finite is a genuine gap, statements only, needs proving from scratch |
| Sec04_27/Problem_4_12.lean | torus_of_revolution_map_isSmoothEmbedding, torus_product_isManifold, etc. | new | Instances/Torus | no | Flat-torus embedding into R^3 fully proved, includes pi-groupoid / product-manifold helpers |
| Sec04_27/Problem_4_3.lean | boundary_rank_normal_form, constant_rank_boundary_local_coordinate_normal_form | new | Manifold/RankTheorem | yes | Constant-rank normal form at boundary points is a genuine gap, but sorry statements and awkward form |
| Sec04_27/Problem_4_6.lean | not_exists_smooth_submersion_to_euclideanSpace | new | Manifold/Submersion | no | Classical result that a compact manifold admits no submersion to R^k fully proved, depends on project predicates |
| Sec04_27/Problem_4_7.lean | contMDiff_iff_comp_equiv_of_submersion_characteristic_property, exists_diffeomorph_of_submersion_characteristic_property | new | Manifold/Submersion | yes | Uniqueness of smooth quotient structure is valuable, but both theorems are sorry |
| Sec04_22/Proposition_4_6.lean | isLocalDiffeomorph_comp, isLocalDiffeomorph_pi, etc. | partial-dup | Manifold/LocalDiffeomorph | yes | Missing composition/product/coordinate-criterion lemmas all sorry, rest is recall |
| Sec04_23/Theorem_4_12.lean | rank_normal_form, constant_rank_local_coordinate_normal_form, etc. | partial-dup | Manifold/RankTheorem | yes | Constant-rank theorem is a genuine gap, but all five proofs sorry and the Euclidean structure needs reworking |
| Sec04_24/Example_4_20.lean | denseTorusCurve, circle_exp_isLocalDiffeomorph_from_angle_branch, etc. | partial-dup | SmoothManifold/CircleExp | no | Irrational-winding counterexample, Circle.exp local-diffeomorphism helper is reusable |
| Sec04_26/Example_4_35.lean | circle_exp_isSmoothCoveringMap, sphere_to_realProjectiveSpace_isCoveringMap, etc. | partial-dup | Instances/CoveringExamples | no | Smooth-covering instances fully proved, RP^n cover is new content and a good example |

</details>

<details><summary>Skip (26 items — mostly Mathlib wrappers / recall files)</summary>

- Sec04_21/Example_4_2.lean — new — all-sorry teaching example
- Sec04_22/Definition_4_22_extra_1.lean — mathlib-dup — pure abbrev restatement
- Sec04_22/Exercise_4_7.lean — mathlib-dup — #check recall only
- Sec04_22/Exercise_4_9.lean — new — Euclidean hardcoded plus sorry
- Sec04_23/Corollary_4_13.lean — new — single-sorry restatement
- Sec04_24/Definition_4_24_extra_1.lean — mathlib-dup — eight lines of #check only
- Sec04_24/Example_4_17.lean — partial-dup — of_opens plus sorry stub
- Sec04_24/Example_4_18.lean — new — single concrete counterexample
- Sec04_24/Example_4_19.lean — new — teaching figure-eight curve counterexample
- Sec04_24/Exercise_4_24.lean — new — one-off counterexample machinery
- Sec04_24/Lemma_4_21.lean — mathlib-dup — re-proves Dirichlet approximation
- Sec04_25/Exercise_4_27.lean — new — x^3 teaching counterexample
- Sec04_25/Exercise_4_32.lean — new — pure recall of 4.31
- Sec04_26/Corollary_4_43.lean — new — sorry stub
- Sec04_26/Exercise_4_34.lean — new — pure recall scaffolding
- Sec04_26/Exercise_4_42.lean — new — pure recall of 4.41
- Sec04_26/Exercise_4_44.lean — new — pure recall of 4.43
- Sec04_26/Exercise_4_45.lean — new — boundary-framework sorry stub
- Sec04_26/Proposition_4_41.lean — new — all-sorry boundary-version main result
- Sec04_27/Problem_4_1.lean — new — thin-wrapper single counterexample
- Sec04_27/Problem_4_10.lean — new — single-sorry statement
- Sec04_27/Problem_4_13.lean — new — statement depends on unproved infrastructure
- Sec04_27/Problem_4_2.lean — mathlib-dup — one-line specialization
- Sec04_27/Problem_4_4.lean — new — pure bookkeeping recall
- Sec04_27/Problem_4_8.lean — new — all-sorry counterexample
- Sec04_27/Problem_4_9.lean — new — pure recall view

</details>

## Summary

Chapter 4 (immersions, submersions, embeddings, and covering maps) is one of the highest port-value chapters in the whole audit: most of the 16 high-value files are completely sorry-free, including the manifold-version inverse function theorem (an explicit Mathlib TODO), the complete definition-layer API for smooth submersions and smooth covering maps, the 700-line major theorem on unique smooth structure lifted along a topological cover, and the full construction of the CP^n quotient submersion together with CP^1 ≅ S^2. The medium-value entries are mostly well-designed but proof-missing statement skeletons (rank theorem, global rank theorem, quotient-manifold characteristic property); porting them amounts to committing to rank-theorem-level proof work. Recommendation: prioritize porting the sorry-free files in blocks following the dependency order Submersion → CoveringMap → InverseFunctionTheorem, then build on them to gradually complete the local-section theorem upstream of IsSmoothSubmersion.

---

---

# Chap05

## Port priority (high, 18 items)

| File | Declarations | Class | Target | sorry | Rationale |
|---|---|---|---|---|---|
| Sec05_28/Definition_5_28_extra_1.lean | IsEmbeddedSubmanifold, IsEmbeddedSubmanifold.codimension, etc. | new | Manifold/Submanifold/Embedded | no | Embedded submanifold class fills a Mathlib gap; needs the Sec05_31 immersion structure |
| Sec05_28/Proposition_5_4.lean | graphMap, graphMap_isSmoothEmbedding, etc. | new | Manifold/Submanifold/Graph | yes | Graph of a smooth map as a smooth embedding; missing from Mathlib, GMT foundation |
| Sec05_29/Definition_5_29_extra_1.lean | Set.euclideanSlice, Set.IsSliceInChart, etc. | new | Manifold/SliceCharts | no | Slice-chart / local-slice-condition API, the bedrock of submanifold theory |
| Sec05_29/Theorem_5_8.lean | local_slice_criterion_for_embedded_submanifold, etc. | new | Manifold/SliceCharts | no | Local k-slice criterion fully proved sorry-free, a Mathlib gap |
| Sec05_30/Proposition_5_16.lean | euclidean_tail_projection, embedded_submanifold_iff_locally_level_set_of_smooth_submersion, etc. | new | Manifold/Submanifold/LocalDefining | yes | Local criterion for submersion level sets; projection lemma proved, main iff still sorry |
| Sec05_31/Definition_5_31_extra_1.lean | Manifold.ImmersedSubmanifold, IsImmersion.toImmersedSubmanifold, etc. | new | Manifold/Submanifold/Immersed | no | Sorry-free bundled immersed-submanifold structure; varifold code benefits directly |
| Sec05_32/Corollary_5_30.lean | IsSmoothEmbedding.contMDiff_toSubtype, contMDiffAt_toSubtype, etc. | new | Manifold/Submanifold | no | General codomain-restriction theorem proved; Mathlib has only the sphere special case |
| Sec05_35/Corollary_5_39.lean | tangent_iff_mfderiv_eq_zero_of_isDefiningFunction, etc. | new | Submanifold/LevelSet | no | Regular-value tangent-space characterization proved, but depends on Proposition 5.38 which contains sorry |
| Sec05_35/Definition_5_35_extra_2.lean | IsInwardPointing, IsBoundaryTangentVector, etc. | new | Boundary/PointingVectors | no | Inward/outward-pointing vector API fills the divergence-theorem gap; definitions need redesign |
| Sec05_35/Notation_5_35_extra_1.lean | Manifold.submanifoldTangentSpace, T[J; p] notation | new | Submanifold/TangentSpace | no | Core definition of the submanifold tangent space, cornerstone of the whole section's theorems |
| Sec05_35/Proposition_5_35.lean | tangentVector_mem_submanifold_iff_exists_curve, etc. | new | Submanifold/TangentSpace | no | Tangent vector as curve velocity, fully proved; needs the Chap03 curve infrastructure |
| Sec05_35/Proposition_5_38.lean | IsLocalDefiningMapOn, tangentSpace_eq_ker_mfderiv_of_isLocalDefiningMapOn | new | Submanifold/LevelSet | yes | Core local-defining-map API on which 5.39/5.40 depend; main theorem sorry |
| Sec05_36/Definition_5_36_extra_4.lean | Set.euclideanHalfSlice, OpenPartialHomeomorph.IsBoundarySliceChart, etc. | new | Manifold/SliceCharts | no | Boundary half-slice-chart API, sorry-free; needs the Sec05_29 counterpart |
| Sec05_36/Theorem_5_51.lean | local_slice_criterion_for_embedded_submanifold_with_boundary, etc. | new | Manifold/SubmanifoldWithBoundary | yes | Boundary k-slice criterion, ~2000 lines, three core sorries to fill |
| Sec05_37/Problem_5_18.lean | immersed_submanifold_isEmbeddedSubmanifold_iff_smoothFunctions_isSmoothOn, etc. | new | Manifold/Submanifold/SmoothExtension | no | Embedded iff smooth functions extend; sorry-free, reusable API |
| Sec05_37/Problem_5_23.lean | IsBoundaryRegularValue, regular_preimage_has_embedded_submanifold_with_boundary_structure, etc. | new | Manifold/Submanifold/RegularValue | yes | Boundary regular-value preimage theorem mostly proved, two lemmas remain sorry |
| Sec05_37/Problem_5_8.lean | basis_model_diffeomorph, regularCoordinateBall_compl_boundary_diffeomorph_sphere, etc. | new | Manifold/CoordinateBall | yes | Regular-coordinate-ball / regular-domain infrastructure nearly complete, only one sorry left |
| Sec05_36/Proposition_5_49.lean | isSmoothEmbedding_of_le, immersed_submanifold_has_embedded_neighborhood, etc. | partial-dup | Manifold/Submanifold | no | Embedded-image induced structure proved, goes beyond Mathlib's SmoothEmbedding |

<details><summary>Consider (medium, 33 items)</summary>

| File | Declarations | Class | Target | sorry | Rationale |
|---|---|---|---|---|---|
| Sec05_28/Proposition_5_2.lean | IsInducedImageManifoldStructure, smooth_embedding_range_has_induced_manifold_structure, etc. | new | Manifold/Submanifold/InducedStructure | yes | Induced structure on the image is foundational, but the theorem is all sorry and the API needs reworking |
| Sec05_28/Proposition_5_3.lean | productSliceMap, productSliceMap_isSmoothEmbedding, etc. | new | Manifold/Submanifold/Product | yes | Slice-embedding x↦(x,p) small lemma usable, main theorem all sorry |
| Sec05_28/Proposition_5_7.lean | smooth_map_graph_isProperlyEmbedded | new | Manifold/Submanifold/Graph | yes | Global graph proper embedding, single sorry, should be ported together with Proposition 5.4 |
| Sec05_29/Exercise_5_10.lean | sphericalCoordinates, sphericalCoordinates_mem_maximalAtlas, etc. | new | Instances/SphericalCoordinates | no | 3D spherical-coordinate chart fully proved, but a concrete chart rather than general infrastructure |
| Sec05_30/Corollary_5_13.lean | smooth_submersion_level_set_has_embedded_submanifold_structure, etc. | new | Manifold/Submanifold/LevelSet | no | Submersion level-set corollary is a thin wrapper, depends on Theorem 5.12 which contains sorry |
| Sec05_30/Corollary_5_14.lean | regular_level_set_has_embedded_submanifold_structure, etc. | new | Manifold/Submanifold/LevelSet | yes | Regular level-set theorem fills a gap, but is all sorry and needs proving from scratch |
| Sec05_30/Definition_5_30_extra_2.lean | Manifold.IsRegularPoint, Manifold.IsCriticalValue, etc. | new | Manifold/Submanifold/RegularValue | yes | Regular/critical-point vocabulary missing, but supporting lemmas all sorry |
| Sec05_30/Definition_5_30_extra_3.lean | Set.IsDefiningMap, Set.IsLocalDefiningMapOn, etc. | new | Manifold/Submanifold/DefiningMap | yes | Defining-map API is a gap, but the class design needs major reworking |
| Sec05_30/Theorem_5_12.lean | constant_rank_level_set_has_embedded_submanifold_structure, etc. | new | Manifold/Submanifold/LevelSet | yes | Constant-rank level-set theorem is a key gap, all sorry, only the statement is portable |
| Sec05_31/Definition_5_31_extra_2.lean | ImmersedSubmanifold.IsLocalParametrization, IsGlobalParametrization, etc. | new | Manifold/Submanifold/Parametrization | yes | Parametrization predicates are novel, but hard-code Fin k, API needs reworking |
| Sec05_31/Exercise_5_20.lean | ImmersedSubmanifold.continuous_inclusion, subspaceTopology_le_givenTopology_iff_isEmbedding, etc. | new | Manifold/Submanifold/Immersed | no | Core API proved, should be ported together with Definition_5_31_extra_1 |
| Sec05_31/Proposition_5_18.lean | injective_immersion_range_has_immersed_submanifold_structure, etc. | new | Manifold/Submanifold/Immersed | yes | Existence-uniqueness of the injective-immersion image structure, statement only, no proof |
| Sec05_31/Proposition_5_22.lean | ImmersedSubmanifold.exists_open_neighborhood_isSmoothEmbedding | new | Manifold/Submanifold/Immersed | yes | Local embedding of immersed submanifolds is useful, but the whole file is a single sorry statement |
| Sec05_31/Proposition_5_23.lean | IsImmersion.isSmoothLocalParametrization_of_mem_maximalAtlas, etc. | new | Manifold/Submanifold/Parametrization | no | Chart gives local parametrization, proved, but bound to definitions awaiting rework |
| Sec05_32/Remark_5_32_extra_1.lean | IsWeaklyEmbeddedSubmanifold instance | new | Manifold/Submanifold | no | Glue instance for embedded implies weakly embedded, must move with the submanifold class |
| Sec05_32/Theorem_5_29.lean | contMDiff_toSubtype_of_isImmersedSubmanifold | new | Manifold/Submanifold | yes | Codomain restriction generalizing Corollary 5.30, statement only, needs proving from scratch |
| Sec05_33/Theorem_5_31.lean | immersed_submanifold_structure_unique_of_same_carrier | new | Manifold/Submanifold | yes | Uniqueness of submanifold structure, sorry statement, needs the full API plus a real proof |
| Sec05_35/Definition_5_35_extra_3.lean | BoundaryDefiningFunction, CoeFun instance | new | Boundary/DefiningFunction | no | Bundled boundary defining function, hard-codes the half-space and duplicates 5.43 |
| Sec05_35/Exercise_5_40.lean | tangentSpace_eq_ker_mfderiv_of_level_set_of_hasConstantRank, etc. | new | Submanifold/LevelSet | yes | Constant-rank level-set tangent space, key lemma sorry and duplicates 5.39 |
| Sec05_35/Exercise_5_44.lean | boundary_defining_derivative, inwardPointing_iff_boundaryDefiningDerivative_pos, etc. | new | Boundary/DefiningFunction | yes | Derivative-sign characterization of inward/outward is the right API, all four theorems sorry |
| Sec05_35/Proposition_5_37.lean | tangentVector_mem_submanifold_iff_forall_smooth_eq_zero | new | Submanifold/TangentSpace | yes | Functional tangent-vector characterization, single sorry, proof needs the extension lemma |
| Sec05_35/Proposition_5_41.lean | boundary_coordinate_component, boundary_vector_trichotomy, etc. | new | Boundary/PointingVectors | yes | Companion theorems for the boundary-vector coordinate trichotomy, all eight sorry |
| Sec05_35/Proposition_5_43.lean | IsBoundaryDefiningFunction, exists_boundary_defining_function | new | Boundary/DefiningFunction | yes | Existence of a global boundary defining function, sorry, duplicates extra_3 |
| Sec05_36/Definition_5_36_extra_2.lean | Set.IsRegularDomain, instIsRegularDomainEmpty | new | Manifold/RegularDomain | no | Regular domain is the divergence-theorem integration domain, needs rebuilding per project scaffolding |
| Sec05_36/Definition_5_36_extra_3.lean | Manifold.IsRegularValue, IsRegularSublevelSet, etc. | new | Manifold/RegularValue | yes | Regular-value concept fills a gap, iff lemma sorry, design needs changing |
| Sec05_36/Proposition_5_46.lean | regular_domain_manifoldInterior_image_eq_interior, etc. | new | Manifold/RegularDomain | yes | Regular-domain interior/boundary correspond to topological interior/frontier, proof all sorry |
| Sec05_37/Problem_5_15.lean | transported_subset_chartedSpace, transported_subset_isManifold_top, etc. | new | Manifold/StructureTransport | no | Family of structure-transport-along-homeomorphism lemmas proved and reusable, counterexample part is textbook-ish |
| Sec05_37/Problem_5_19.lean | curve_velocity_mem_embedded_submanifold_tangent, etc. | new | Manifold/Submanifold/Tangent | no | Curve velocity lands in the tangent subspace, proved; half the file is a counterexample |
| Sec05_37/Problem_5_4.lean | continuous_injective_interval_to_curve_manifold_isEmbedding, etc. | new | Manifold/CurveEmbedding | no | 1D invariance-of-domain auxiliary lemma, sorry-free, missing from Mathlib |
| Sec05_37/Problem_5_5.lean | continuous_injective_real_to_curve_manifold_isEmbedding, etc. | new | Manifold/CurveEmbedding | no | Real line into a 1-manifold embedding lemma proved, should be combined with 5.4 into one module |
| Sec05_37/Problem_5_6.lean | unitTangentBundle, unitTangentBundle_exists_isSmoothEmbedding, etc. | new | TangentBundle/UnitTangentBundle | yes | Unit tangent bundle absent everywhere, but main theorem all sorry, only an API seed |
| Sec05_28/Proposition_5_1.lean | open_submanifold_isEmbeddedSubmanifold, etc. | partial-dup | Manifold/Submanifold/Open | yes | Partly duplicates Mathlib of_opens, converse all sorry and needs generalizing |
| Sec05_32/Definition_5_32_extra_2.lean | IsImmersedSubmanifold, IsWeaklyEmbeddedSubmanifold, etc. | partial-dup | Manifold/Submanifold | no | Submanifold predicate classes fill a gap, API needs reworking and one helper duplicates Mathlib |

</details>

<details><summary>Skip (34 items — mostly Mathlib wrappers / recall files)</summary>

- Sec05_28/Corollary_5_6.lean — mathlib-dup — one-line composition of an existing lemma
- Sec05_28/Definition_5_28_extra_2.lean — partial-dup — thin naming abbreviation
- Sec05_28/Proposition_5_5.lean — mathlib-dup — only a #check wrapper
- Sec05_29/Example_5_9.lean — partial-dup — sphere API rewrapped
- Sec05_29/Remark_5_29_extra_2.lean — new — only a sorry-statement remark
- Sec05_29/Remark_5_29_extra_3.lean — new — recall cross-reference
- Sec05_30/Definition_5_30_extra_1.lean — mathlib-dup — recall of the preimage concept
- Sec05_30/Example_5_15.lean — mathlib-dup — pedagogical sphere restatement
- Sec05_30/Example_5_17.lean — new — torus example all sorry
- Sec05_31/Example_5_19.lean — new — figure-eight counterexample, no API
- Sec05_31/Example_5_25.lean — new — #check plus trivial corollary
- Sec05_31/Example_5_26.lean — new — figure-eight scaffolding with sorry
- Sec05_31/Exercise_5_24.lean — new — only recall/#check
- Sec05_32/Example_5_28.lean — new — figure-eight counterexample, key sorry
- Sec05_32/Theorem_5_27.lean — mathlib-dup — recall plus a one-line specialization
- Sec05_34/Notation_5_34_extra_1.lean — mathlib-dup — pure notation reference
- Sec05_35/Definition_5_35_extra_4.lean — new — R²-specific scaffolding
- Sec05_35/Example_5_45.lean — new — single plane-curve example
- Sec05_35/Exercise_5_36.lean — new — pure recall restatement
- Sec05_35/Exercise_5_42.lean — new — recall sorry statement
- Sec05_36/Definition_5_36_extra_1.lean — mathlib-dup — #check predicate restatement
- Sec05_36/Exercise_5_50.lean — partial-dup — recall reproof combination
- Sec05_36/Exercise_5_52.lean — partial-dup — recall re-derivation
- Sec05_36/Exercise_5_54.lean — partial-dup — recall pointer
- Sec05_36/Remark_5_36_extra_5.lean — partial-dup — remark with no declarations
- Sec05_36/Theorem_5_53.lean — partial-dup — one-line wrapper with sorry
- Sec05_37/Problem_5_1.lean — new — concrete exercise, no API
- Sec05_37/Problem_5_10.lean — new — cubic curve, 17 sorries
- Sec05_37/Problem_5_11.lean — new — concrete zero set all sorry
- Sec05_37/Problem_5_12.lean — partial-dup — new part all sorry
- Sec05_37/Problem_5_13.lean — new — one-off counterexample with sorry
- Sec05_37/Problem_5_20.lean — new — figure-eight counterexample, no API
- Sec05_37/Problem_5_7.lean — new — single-example classification with sorry
- Sec05_37/Problem_5_9.lean — new — single sorry statement

</details>

## Summary

This chapter (Chapter 5: submanifold theory) is the highest-value chapter to port in the entire audit: embedded/immersed submanifold classes, slice-chart criteria, submanifold tangent spaces, local defining maps, and boundary-vector APIs — 18 high-value files in total, almost all Mathlib gaps and more than half sorry-free, directly able to support OpenGALib's GMT and divergence-theorem gaps. The recommendation is to use the three main lines SliceCharts, Submanifold/Immersed+Embedded, and Submanifold/TangentSpace as the skeleton, porting the sorry-free files first, then using the level-set and boundary series from the medium table to fill in the statement layer. The low-value entries are mostly concrete textbook counterexamples and recall scaffolding, and can be skipped wholesale.

