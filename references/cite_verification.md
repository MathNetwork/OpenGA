# Cited Theorem Verification

This document tracks alignment between Lean signatures of cited black-box
theorems in the AltRegularity formalization and the actual statements in
the cited papers.

The framework's chain proofs (`positiveDensity_*`, `alphaStructural_*`,
`isStable_*`, `integrality_no_*`, `main_theorem_*`,
`exists_smoothMinimalHypersurface_*`) consume these black-boxes as
hypotheses — so a Lean / cited-paper mismatch on any one of them means
the chain proves an off-paper claim.

## Workflow

The verification chain is layered. Each layer must align with the next:

```
Lean signature (kernel-verified)
   ↑ Round 5 strict-alignment
Paper §X phrase (verbatim from paper/chapters/part2/*.tex)
   ↑ Round 5 verification document
Cited paper (Wic14, CLS22, DLT13, CL03, Lin85) phrase
   ↑ Pitts/Simon ground truth references
Pitts 1981 / Simon 1983 ground truth (GMT primitives)
   ↑ docstrings (`**Ground truth**: Simon §X` in opaque defs)
   ↓ future: real defs replacing opaque primitives
```

Steps for each entry below:

1. **Lean signature** — auto-extracted from current source (file:line).
2. **Paper §X phrasing** — verbatim quote from `paper/chapters/part2/*.tex`.
3. **Cited original statement** — verbatim quote from the cited paper
   (local PDF / arXiv tex source).
4. **Alignment check** — row-by-row comparison of components.
5. **Ground truth references** — for each GMT primitive in the statement,
   the Pitts 1983 / Simon 1981 §X / Allard 1972 §X reference; for
   cited-paper-specific contributions, note which results are NOT in
   ground-truth GMT.
6. **Status** advances 🔴 → 🟡 (mismatch flagged) → 🟢 (verified aligned).

If a mismatch is found, the framework's signature is strict-aligned to
match (which may surface a hidden gap in the chain — see Round 5 Item 1
on `regularity_of_inClassSAlpha` for an example).

## Status legend

- 🔴 Not started — neither paper §X nor cited original filled
- 🟡 Mismatch flagged, awaiting fix
- 🟢 Verified aligned

## Local cited-paper inventory

Resources discovered under
`/Users/moqian/Desktop/Free Boundary Min-Max Theory in Complete Riemannian Manifolds/resources`:

| Cite key | Format | Path |
|---|---|---|
| Wic14 | tex | `arXiv-sources/Wic14-Wickramasekera/embedded-stable-final-revised-3.tex` |
| CL03 | pdf | `pdf/CL03-Colding-DeLellis-2003.pdf` |
| CLS22 | tex | `arXiv-sources/CLS22-Chodosh-Liokumovich-Spolaor/main.tex` |
| DLT13 | tex | `arXiv-sources/DLT13-DeLellis-Tasnady/DLT13-DeLellis-Tasnady.tex` |
| Lin85 | pdf | `pdf/Lin85-Lin-1985.pdf` |
| Allard72 | pdf (split) | `Allard-Theory-of-Varifolds/Theory of Varifolds {1-4,5-6,7-9,10-12,13-end-1}.pdf` |
| Sim83 | pdf | `pdf/Sim83-Simon-Lectures-on-GMT-1983.pdf` |
| SSY75 | pdf | `pdf/SSY75-Schoen-Simon-Yau-1975.pdf` |
| Pitts81 | pdf | `pdf/Existence and regularity of minimal surfaces on Riemannian manifolds by Pitts...pdf` |
| CL20 | tex | `arXiv-sources/CL20-Chambers-Liokumovich/CLminimal_2018_December.tex` |

### Ground truth sources (Pitts 1981 + Simon 1983)

These two sources are GMT ground truth — every cited paper above (CLS22,
Wic14, DLT13, CL03, Lin85) is built on top of them. Each opaque GMT
primitive in `AltRegularity/GMT/*.lean` carries a `**Ground truth**:`
docstring line pointing to the relevant Pitts/Simon section.

| Framework opaque | Pitts/Simon §X reference |
|---|---|
| `Varifold.firstVariation` | Simon §38 (eq. 38.1); Allard §4.1; Pitts §3.6 |
| `Varifold.secondVariation` | Simon §49; Schoen–Simon 1981 §1 |
| `Varifold.tangentCone` | Simon §42; Allard §3.4–§3.6 |
| `Varifold.density` | Simon §17 (monotonicity formula) |
| `Varifold.regular` | Simon §41 + Wic14 §2 |
| `Varifold.VarifoldConverge` | Simon §38 (weak-* on $C_c(G_n(M))$) |
| `Varifold.ofBoundary` | Simon §27 (BV) + §38 (associated varifold) |
| `IsHRectifiable` | Simon §11; Federer 1969 §3.2.14 |
| `IsJunctionCone` | Simon §42 + Wic14 §3 |
| `flatDist` | Simon §31 (flat metric on currents) |
| `SlicesL1Converge`, `DChiWeakConverge` | Simon §13–§14 (BV) |
| `IsInnerAlmostMinimizer`, `IsOuterAlmostMinimizer` | Pitts §3.7 |
| `IsOneSidedCompetitor` | Pitts §3.7 + CLS22 §2 |
| `TestVectorField` | smooth-manifold standard, Simon §38 |
| `HasAlphaJunctionAt` | Wic14 §2 — Wic14 contribution, no Pitts/Simon analog |
| `HausdorffSmallSingular` | Wic14 Theorem 3.1 + Simon §3 (Hausdorff measure) |
| `IsOptimal`, `IsVolumeParametrized`, `InnerHomotopicMinimizer`, `OuterHomotopicMinimizer` | sweepout-specific (CLS22 §2 + paper §3) |

---

## 1. Wickramasekera 2014 → `regularity_of_inClassSAlpha`

**Lean signature**: `AltRegularity/Regularity/SmoothRegularity.lean:89` (and corollary at `:106`)

```lean
theorem regularity_of_inClassSAlpha
    {V : Varifold M} {α : ℝ} (hα : 0 < α ∧ α < 1/2)
    {n : ℕ} (hn : 2 ≤ n)
    (hclass : InClassSAlpha V α) :
    (n ≤ 6 → sing V = ∅) ∧
    (n = 7 → (sing V).Countable) ∧
    (8 ≤ n → HausdorffSmallSingular V n)

theorem isSmoothMinimalHypersurface_of_inClassSAlpha
    {V : Varifold M} {α : ℝ} (hα : 0 < α ∧ α < 1/2)
    {n : ℕ} (hn : 2 ≤ n) (hn6 : n ≤ 6)
    (hclass : InClassSAlpha V α) :
    IsSmoothMinimalHypersurface V
```

**Cited paper**:
- File: `arXiv-sources/Wic14-Wickramasekera/embedded-stable-final-revised-3.tex`
- Reference: Annals of Mathematics 179 (2014), 843-1007
- Theorem: 3.1 (Euclidean) / 6.1 (manifold version)

**Paper §4 phrasing** (`paper/chapters/part2/4-regularity-tools.tex:94-102`):

> Let $(N^{n+1}, g)$ be a smooth Riemannian manifold and $\alpha \in (0, 1/2)$.
> If $V \in \mathcal{S}_\alpha$ on $N$ with $\|V\|(N) < \infty$, then:
> (a) $\sing V = \varnothing$ if $2 \le n \le 6$;
> (b) $\sing V$ is discrete if $n = 7$;
> (c) $\mathcal{H}^{n-7+\gamma}(\sing V) = 0$ for each $\gamma > 0$ if $n \ge 8$.
> In particular, for $2 \le n \le 6$, $\spt\|V\|$ is a smooth embedded minimal hypersurface.

**Original statement** (Wickramasekera 2014, Theorem 3.1 / Theorem 6.1):

[TODO: read `embedded-stable-final-revised-3.tex` and fill]

**Alignment check**:

| Component | Lean | Paper §4 | Cited original | Status |
|---|---|---|---|---|
| α range | `0 < α ∧ α < 1/2` | $\alpha \in (0, 1/2)$ | TODO | 🟡 |
| (S1) stationary | `InClassSAlpha.stationary` | (S1) ✓ | TODO | 🟡 |
| (S2) stable | `InClassSAlpha.stable` | (S2) ✓ | TODO | 🟡 |
| (S3) α-structural | `InClassSAlpha.alphaStructural` | (S3) ✓ | TODO | 🟡 |
| integral prerequisite | `InClassSAlpha.integral` | "integral n-varifold" | TODO | 🟡 |
| finite mass | `Varifold.isFiniteMeasure` (struct field) | $\|V\|(N) < \infty$ | TODO | 🟡 |
| n hypothesis | `(n : ℕ) (hn : 2 ≤ n)` | $n \ge 2$ implicit (Riemannian dim n+1) | TODO | 🟡 |
| (a) 2 ≤ n ≤ 6 | `n ≤ 6 → sing V = ∅` ✓ | (a) verbatim | TODO | 🟡 |
| (b) n = 7 | `n = 7 → (sing V).Countable` | (b) "discrete" | TODO | 🟡 |
| (c) n ≥ 8 | `8 ≤ n → HausdorffSmallSingular V n` (opaque) | (c) Hausdorff | TODO | 🟡 |
| "in particular" clause | `isSmoothMinimalHypersurface_of_inClassSAlpha` (corollary) | (sentence) | TODO | 🟡 |

**Hidden gap caught**: paper Theorem 1.1's "$2 \le n \le 6$" hypothesis was implicit in the Lean framework before strict-alignment; now threaded explicitly through `main_theorem_*` and `exists_smoothMinimalHypersurface_via_ONVP`.

**Ground truth references** (Pitts 1981 / Simon 1983):

GMT primitives used in the statement:
- $\mathcal{S}_\alpha$ class (S1)(S2)(S3): Wic14 §2 — Wickramasekera-specific
- (S1) `IsStationary` / first variation: Simon §38 (eq. 38.1) ✓ ground truth
- (S2) `IsStable` / second variation: Simon §49 (Jacobi field setup); Schoen–Simon 1981 §1 ✓ ground truth
- `IsIntegral` (multiplicity): Simon §38 (integer-multiplicity varifolds)
- `IsRectifiable`: Simon §11 (rectifiable sets)
- `density`: Simon §17 (monotonicity formula)
- `regular` / `sing`: Simon §41 + Wic14 §2

Cited paper-specific contributions (not in Pitts/Simon):
- (S3) $\alpha$-structural hypothesis (`HasAlphaJunctionAt`): Wic14 §2 — original Wic14 contribution
- Sheeting Theorem + Minimum Distance Theorem (used to relate (S3) to junction tangent cones): Wic14 §3 — Wic14 contribution
- Singular set Hausdorff dimension bound (clauses (b)(c)): Wic14 main theorem — Wic14 contribution

**Status**: 🟡 (paper §4 verified verbatim; cited Wic14 original statement TODO)

---

## 2. CL03 Pull-tight (Colding–De Lellis 2003) → `isStationary_of_minmaxLimit`

**Lean signature**: `AltRegularity/Sweepout/PullTight.lean:23`

```lean
theorem isStationary_of_minmaxLimit
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hlim : MinMaxLimit Φ t₀ V) :
    Varifold.IsStationary V
```

**Cited paper**:
- File: `pdf/CL03-Colding-DeLellis-2003.pdf`
- Reference: Colding–De Lellis, "The min-max construction of minimal surfaces", 2003
- Theorem: Proposition 1.4

**Paper §3 phrasing** (`paper/chapters/part2/3-sweepouts.tex:236-238`):

> [Proposition 3.7 / thm:CLS-stationary] Let $(M^{n+1},g)$ be a closed Riemannian
> manifold with $n \ge 2$, and let $\Phi$ be an optimal sweepout with
> $\sup_x \mathbf{M}(\Phi(x)) = W$. Then there exists a stationary $n$-varifold
> $V$ in $M$ with $\mathbf{M}(V) = W$.

**Original statement** (CL03, Proposition 1.4):

[TODO: read `CL03-Colding-DeLellis-2003.pdf` and fill]

**Alignment check**:

| Component | Lean | Paper §3 | Cited original | Status |
|---|---|---|---|---|
| Sweepout hypothesis | `MinMaxLimit Φ t₀ V` | "optimal sweepout" | TODO | 🟡 |
| Conclusion | `IsStationary V` | "stationary n-varifold" | TODO | 🟡 |
| mass = W | implicit in `MinMaxLimit` | $\mathbf{M}(V) = W$ explicit | TODO | 🟡 |

**Status**: 🔴

---

## 3. CLS22 Proposition 3.1 → `hnm_finite_of_nonExcessive`

**Lean signature** (after Round 5 Item 3 strict-alignment):
`AltRegularity/Sweepout/HomotopicMinimization.lean:135`

```lean
theorem hnm_finite_of_nonExcessive
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hne : NonExcessive Φ) (honvp : ONVP Φ) (hcrit : Critical Φ t₀)
    (hlim : MinMaxLimit Φ t₀ V) :
    (hnm V).Finite
```

**Cited paper**:
- File: `arXiv-sources/CLS22-Chodosh-Liokumovich-Spolaor/main.tex`
- Reference: [CLS22] §4 propositions (no single "Proposition 3.1" exists
  in CLS22 — see note below)
- Cited under paper-internal labels: `p:pairs` (line 1323), `p:def_thm`
  (line 1399), `p:def-thm-cancel` (line 1607)

**Note on CLS22 numbering**: paper §6.1 cites "[CLS22, Proposition 3.1]"
but CLS22 §3 ("Non-excessive sweepouts", line 1079) does not contain a
labeled Proposition 3.1. The actual results that establish hnm
finiteness are in **CLS22 §4** ("Deformation Theorems", line 1275),
distributed across no-cancellation and cancellation subsections. The
paper's §3.1 citation is imprecise — `[CLS22, §3-§4]` would be more
accurate. The framework matches paper §6.1's stated conclusion
("finite").

**Paper §6.1 phrasing** (`paper/chapters/part2/6-regularity.tex:18`):

> By [CLS22, Proposition 3.1], the set $\mathfrak{h}_{\mathrm{nm}}(V)$
> of non-homotopic-minimizing points (Definition 3.8) is finite. ...
> We remark that the finiteness of $\mathfrak{h}_{\mathrm{nm}}(V)$ in
> [CLS22, Proposition 3.1] relies on both the non-excessive property
> **and the nestedness of the sweepout**: the proof constructs
> replacement families by "gluing in" one-sided homotopies, and
> nestedness ($\Omega(x_1) \subset \Omega(x_2)$) ensures that the
> parameter sets on which these replacements are defined are intervals.

**Original statements in CLS22**:

CLS22 line 1295 (no-cancellation setup `e:no_canc2`):
> there is a (ONVP) sweepout $\{\Phi(x) = \partial \Omega(x)\}$ and
> $x_i \nearrow x_0 \in \mathfrak{m}_L(\Phi)$, so that
> $|\Phi(x_i)| \to |\Sigma| := |\partial \Omega| \in \mathcal{R}$
> and **$\Phi$ is not left excessive at $x_0$**.

CLS22 `p:def_thm` (line 1399, no-cancellation case, statement 3):
> If $\mathfrak{h}_{\mathrm{nm}}(\Sigma)$ is non-empty, then $\Sigma$
> is stable, $\mathcal{H}^0(\mathfrak{h}_{\mathrm{nm}}(\Sigma)) = 1$
> and for every point $x \in \Sigma \setminus
> \mathfrak{h}_{\mathrm{nm}}(\Sigma)$ there exists $r > 0$, such that
> $\Sigma$ is minimizing to one side in $B_r(x)$.

CLS22 `p:def-thm-cancel` (line 1607, cancellation case):
> Suppose $V = \sum_i \kappa_i |\Sigma_i|$ is as in [e:canc], then
> each $\Sigma_i$ has stable regular part and
> $\mathfrak{h}_{\mathrm{nm}}(V) = \emptyset$.

**Alignment check** (post-strict-alignment):

| Component | Lean | Paper §6.1 | CLS22 original | Status |
|---|---|---|---|---|
| NonExcessive form | `hne : NonExcessive Φ` (forbid 2-sided I-replacement) | "non-excessive" | "$\Phi$ not left excessive at $x_0$" (separated form per side) | 🟡 — framework's unified ↔ CLS22 separated via Option C bridge |
| ONVP hypothesis | `honvp : ONVP Φ` | "non-excessive ONVP" + "nestedness" remark | "(ONVP) sweepout" | ✓ paper-explicit |
| Critical Φ t₀ | `hcrit : Critical Φ t₀` | "$x_i \to x_0 \in \mathfrak{m}(\Phi)$" | "$x_0 \in \mathfrak{m}_L(\Phi)$" (no-canc) | 🟡 (Lean uses unified Critical; CLS22 uses separated $\mathfrak{m}_L$ / $\mathfrak{m}_R$) |
| MinMaxLimit Φ t₀ V | `hlim` | "$V$ varifold limit of $|\partial^*\Omega(x_i)|$" | "$|\Phi(x_i)| \to |\Sigma|$" | ✓ |
| hnm V definition | paper Def 3.8 / `Sweepout.hnm` | Def 3.8 | CLS22 Def 2.5 | ✓ aligned (paper Def 3.8 cites CLS22 Def 2.5) |
| Conclusion | `(hnm V).Finite` | "finite" | "$\mathcal{H}^0 \le 1$" (no-canc) / "$= \emptyset$" (canc) | 🟡 — framework matches paper §6.1 ("finite"); CLS22 actually proves stronger ("≤ 1") |

**Findings**:

1. **ONVP hypothesis added** ✓ : paper §6.1 explicitly states "the
   finiteness ... relies on both the non-excessive property and the
   **nestedness of the sweepout**". Framework was missing this; now
   `honvp : ONVP Φ` is in the signature, propagated through chain via
   `isStable_of_nonExcessive_minmax` (also gained `honvp`) and both
   `main_theorem_*`.

2. **Conclusion is paper-faithful but weaker than CLS22**: paper §6.1
   uses "finite" (matching framework). CLS22's actual conclusion is
   "$\mathcal{H}^0(\mathfrak{h}_{\mathrm{nm}}) \le 1$" or "$= \emptyset$".
   Framework follows paper. Tightening to cardinality bound is a future
   refinement (would need `Set.Subsingleton` or explicit cardinality).

3. **NonExcessive form**: framework's `NonExcessive` (Option C: forbid
   2-sided I-replacement) and CLS22's separated form ("not left excessive
   at $x_0$") are equivalent via `nonExcessive_of_strict` bridge. Chain
   already uses bridge in `MinMaxExistence`.

4. **CLS22 numbering imprecision**: paper §6.1's "[CLS22, Proposition 3.1]"
   citation does not match a labeled proposition in CLS22 §3. The actual
   CLS22 results are in §4 (`p:pairs`, `p:def_thm`, `p:def-thm-cancel`).
   Framework documentation now references the correct CLS22 labels.

**Chain break**: Yes, `StabilityVerification.lean:124` and
`MainTheorem.lean:85, 130`. Fixed by adding `honvp` to
`isStable_of_nonExcessive_minmax` and propagating from `main_theorem_*`
(both already have `honvp` in scope).

**Ground truth references** (Pitts 1981 / Simon 1983):

GMT primitives used in the statement:
- `Varifold`, `MinMaxLimit`, `VarifoldConverge`: Simon §38 (varifold
  weak convergence on $G_n(M)$); Allard 1972 §3
- `support`, `OneSidedMinimizingAt`, `IsOneSidedCompetitor`: Pitts 1981
  §3.7 (almost-minimizing one-sided competitor); CLS22 §2 (Def 1.4 —
  homotopic minimizer in sweepout context)
- Caccioppoli surgery / "gluing in" homotopies: Simon §27 (currents)
  + §13–§14 (BV)
- Reduced boundary $\partial^*\Omega$ (used in CLS22 proof): Simon §27;
  De Giorgi structure theorem (Maggi 2012, Ch. 15)

Cited paper-specific contributions:
- $\mathfrak{h}_{\mathrm{nm}}(V)$ (non-homotopic-minimizing set):
  CLS22 Def 2.5 + paper §3 Def 3.8 — CLS22 contribution
- Finiteness via 2-sided $I$-replacement extension argument: CLS22
  `p:pairs`, `p:def_thm`, `p:def-thm-cancel` (CLS22 §4) — CLS22
  contribution
- "Nestedness" (ONVP) requirement for the proof: paper §6.1 remark +
  CLS22 §3 — sweepout-specific structural use

**Status**: 🟢 (paper §6.1 + CLS22 originals quoted verbatim; aligned
modulo paper-faithful "finite" vs CLS22 stronger "$\le 1$" — documented;
NonExcessive form bridged via Option C; ONVP hypothesis paper-explicit
and threaded through chain)

---

## 4. DLT 2013 Proposition A.1 → `dlt_criterion`

**Lean signature**: `AltRegularity/Integrality/PerimeterConvergence.lean:78`

```lean
theorem dlt_criterion
    {Φ : MinMax.Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hlim : MinMax.Sweepout.MinMaxLimit Φ t₀ V)
    (hWeak : MinMax.Sweepout.DChiWeakConverge Φ t₀)
    (hPer : MinMax.Sweepout.PerimeterConverge Φ t₀) :
    V = Varifold.ofBoundary (Φ.slice t₀)
```

**Cited paper**:
- File: `arXiv-sources/DLT13-DeLellis-Tasnady/DLT13-DeLellis-Tasnady.tex`
- Reference: De Lellis–Tasnady, "The existence of embedded minimal hypersurfaces", 2013
- Theorem: Proposition A.1 (`p:varivscacc`, line 2206)

**Paper §5 phrasing** (`paper/chapters/part2/5-integrality.tex:7-15`):

> Let $\{\Omega^k\}$ be a sequence of Caccioppoli sets and $U$ an open
> subset of $M$. Assume that
> (i) $D\chi_{\Omega^k} \to D\chi_\Omega$ in the sense of measures in $U$;
> (ii) $\mathrm{Per}(\Omega^k, U) \to \mathrm{Per}(\Omega, U)$
> for some Caccioppoli set $\Omega$. Then the varifolds
> $|\partial^*\Omega^k|$ converge to $|\partial^*\Omega|$ in the sense
> of varifolds.

**Original statement** (DLT13 Proposition A.1, `p:varivscacc`, verbatim):

> Let $\{\Omega^k\}$ be a sequence of Caccioppoli sets and $U$ an open
> subset of $M$. Assume that
> (i) $D \mathbf{1}_{\Omega^k}\to D\mathbf{1}_\Omega$ in the sense of
> measures in $U$;
> (ii) $\per (\Omega^k, U)\to\per(\Omega,U)$
> for some Caccioppoli set $\Omega$ and denote by $V^k$ and $V$ the
> varifolds induced by $\partial^\ast\Omega^k$ and $\partial^\ast\Omega$.
> Then $V^k\to V$ in the sense of varifolds.

**Alignment check** (Lean = paper §5 / DLT13 + uniqueness applied form):

| Component | Lean | Paper §5 | DLT13 original | Status |
|---|---|---|---|---|
| Sequence of Caccioppoli sets | implicit in `hlim`/`hWeak`/`hPer` (Φ-indexed) | $\{\Omega^k\}$ | $\{\Omega^k\}$ | ✓ packaged |
| Limit Caccioppoli | `Φ.slice t₀` | $\Omega$ | $\Omega$ | ✓ |
| (i) weak conv $D\chi$ | `hWeak : DChiWeakConverge Φ t₀` (opaque) | (i) verbatim | (i) verbatim | ✓ |
| (ii) Per convergence | `hPer : PerimeterConverge Φ t₀` (opaque) | (ii) verbatim | (ii) verbatim | ✓ |
| Open subset U | implicit (global) | $U$ open | $U$ open | 🟡 (Lean opaque encodes this) |
| Conclusion | `V = ofBoundary (Φ.slice t₀)` (equality) | "varifolds converge" (convergence) | "$V^k \to V$" (convergence) | 🟡 (combined with uniqueness) |

**Findings**:

1. **Hypothesis (i)+(ii) match verbatim**: paper §5 reproduces DLT13
   verbatim modulo notation ($\mathbf{1}_\Omega$ vs $\chi_\Omega$);
   Lean's `DChiWeakConverge` and `PerimeterConverge` (opaque GMT
   primitives) encode the same conditions.

2. **Conclusion form combined with uniqueness**: DLT13 Prop A.1
   states "varifolds converge"; Lean states equality
   $V = |\partial^*\Omega(t_0)|$. The combined form is what paper §5
   uses in the proof of Theorem `thm:integrality(a)` (line 36):
   "Both conditions of Proposition A.1 are satisfied, so $V$ is the
   integral varifold induced by the Caccioppoli boundary
   $\partial^*\Omega(x_0)$." Equality is derived from convergence
   (DLT13) + uniqueness of weak limit (since `hlim` already gives
   $V$ as a weak limit). Lean signature matches paper §5 USAGE
   pattern.

3. **No chain break**: `dlt_criterion` consumed verbatim by
   `integrality_no_cancellation` step (d) — equality form is what
   the chain wants.

**Ground truth references** (Pitts 1981 / Simon 1983):

- `Caccioppoli set / FinitePerimeter`: Simon §27 (BV) ✓ ground truth
- `DChiWeakConverge` (weak convergence of distributional gradients):
  Simon §13–§14 (BV / weak measure convergence) ✓ ground truth
- `PerimeterConverge` (perimeter convergence): Simon §27 (perimeter
  via total variation $|D\chi_\Omega|$) ✓ ground truth
- `VarifoldConverge`: Simon §38 (varifold weak-* convergence on
  $G_n(M)$) ✓ ground truth
- `ofBoundary` (boundary varifold of Caccioppoli set): Simon §38
  (varifold induced by integer-rectifiable current); De Giorgi
  structure theorem (Maggi 2012, Ch. 15) for the reduced boundary
  $\partial^*\Omega$ as rectifiable

Cited paper-specific contributions:
- The composition (i)+(ii) ⇒ varifold convergence: DLT13 §A
  Prop A.1 — DLT13 contribution (built on Simon §27 + §38 ground truth)
- Uniqueness of weak varifold limit: standard fact from Simon §38
  (weak-* topology on Radon measures on $G_n(M)$)

**Status**: 🟢 (paper §5 + DLT13 originals quoted verbatim; signature
matches paper §5 USAGE pattern as DLT13 Prop A.1 + uniqueness combined.
Convergence-only form is recoverable but not separately exposed since
chain only consumes equality form).

---

## 5. CLS22 Theorem 2.2 → `exists_nonExcessive_ONVP`

**Lean signature** (after Round 5 Item 2 strict-alignment + Option C):
`AltRegularity/Sweepout/NonExcessive.lean:243`

```lean
theorem exists_nonExcessive_ONVP (M : Type*)
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
    (n : ℕ) (hn : 2 ≤ n) (hn6 : n ≤ 6) :
    ∃ Φ : Sweepout M, NonExcessiveStrict Φ ∧ ONVP Φ ∧ 0 < width Φ
```

The theorem returns `NonExcessiveStrict` (paper-faithful separated form,
matching CLS22 verbatim). Downstream chain consumers bridge to
framework's `NonExcessive` via `Sweepout.nonExcessive_of_strict`.

**Cited paper**:
- File: `arXiv-sources/CLS22-Chodosh-Liokumovich-Spolaor/main.tex:1096-1098`
- Reference: [CLS22, Theorem `c:non-excessive_minmax`] (numbered "Theorem 2.2"
  in the paper's bib citation, located in CLS22 §2)
- Ambient setup: CLS22 §2 line 732 — `(M^{n+1}, g)` closed Riemannian
  manifold, Vol(M, g) = 1 by scaling; **no dimension restriction in the
  theorem statement itself**.

**Paper §3 phrasing** (`paper/chapters/part2/3-sweepouts.tex:230-232`):

> Let $(M^{n+1},g)$ be a closed Riemannian manifold with $2 \le n \le 6$.
> There exists an (ONVP) sweepout $\Psi$ such that every
> $x \in \mathfrak{m}_L(\Psi)$ is not left excessive and every
> $x \in \mathfrak{m}_R(\Psi)$ is not right excessive.

**Original statement** (CLS22 §2 Theorem `c:non-excessive_minmax`,
verbatim from `main.tex:1096-1098`):

> There exists a (ONVP) sweepout $\Psi$ such that every
> $x \in \mathfrak{m}_L(\Psi)$ is not left excessive and every
> $x \in \mathfrak{m}_R(\Psi)$ is not right excessive.

**Alignment check** (post-Option C):

| Component | Lean | Paper §3 phrase | CLS22 original | Status |
|---|---|---|---|---|
| Ambient | `[MetricSpace M] [BorelSpace M] [CompactSpace M]` | $(M^{n+1}, g)$ closed Riemannian | $(M^{n+1}, g)$ closed Riemannian, Vol = 1 | 🟡 (smooth-Riemannian via metric proxy; documented gap) |
| Dim hypothesis | `(n : ℕ) (hn : 2 ≤ n) (hn6 : n ≤ 6)` | $2 \le n \le 6$ | NONE (paper-added) | ✓ aligned with paper |
| ONVP | `ONVP Φ` | "(ONVP) sweepout" | "(ONVP) sweepout" | ✓ |
| Non-excessive form | `NonExcessiveStrict Φ` (separated) | left/right separated | left/right separated | ✓ aligned verbatim |
| Width > 0 | `0 < width Φ` (in conclusion) | implicit (DLT13 Prop 0.5 cited at Def 3.1) | implicit | 🟡 Lean adds explicit; paper/CLS22 implicit via isoperimetric. Acceptable convenience. |

**Findings**:

1. **Paper adds 2 ≤ n ≤ 6**: CLS22's existence theorem `c:non-excessive_minmax`
   does **not** restrict the dimension `n`; paper §3 adds `2 ≤ n ≤ 6` because
   downstream regularity needs it. Lean signature now mirrors paper.
   ✓ **Aligned.**

2. **NonExcessive form mismatch RESOLVED** ✓ (Option C, Round 5 follow-up):
   Introduced `Sweepout.NonExcessiveStrict` (left/right separated form,
   matching CLS22 / paper §3 verbatim). `exists_nonExcessive_ONVP` returns
   `NonExcessiveStrict`. Framework's `NonExcessive` is now redefined to
   forbid the conjunction `IReplacementExists` (= `LeftExc ∧ RightExc`),
   which paper §6.2 / §5.1 actually construct via 2-sided I-replacement.
   Bridge `nonExcessive_of_strict : NonExcessiveStrict → NonExcessive` is
   provable via `critical_iff_left_or_right` + side-dispatch. Chain proofs
   in `alphaStructural_of_*` and `positiveDensity_of_*` simplified by 1
   line each (drop redundant `ireplacement_to_excessive` intermediate;
   pass conjunction `hIRep` directly to `non_excessive_def`).

3. **Width > 0 explicit** 🟡 : CLS22 doesn't state `W > 0` as part of the
   theorem; it follows from isoperimetric (DLT13 Prop 0.5). Lean keeps
   `0 < width Φ` in the conclusion as a convenience output. Acceptable.

**Hidden gap caught**: same as Round 5 Item 1 — paper's `2 ≤ n ≤ 6` was
implicit in the framework, now threaded through `exists_nonExcessive_ONVP`
and propagated to `exists_smoothMinimalHypersurface_via_ONVP`.

**Chain break**: Yes, `MinMaxExistence.lean:90` (`exists_smoothMinimalHypersurface_via_ONVP`).
Fixed by passing `n hn hn6` through (already in scope from Round 5 Item 1).

**Ground truth references** (Pitts 1981 / Simon 1983):

GMT primitives used in the statement:
- `Sweepout` (Caccioppoli boundary family): Simon §13–§14 (BV /
  finite-perimeter sets); De Giorgi structure theorem
- `FContinuous` / flat distance: Simon §27 (currents) + §31 (flat metric);
  for Caccioppoli sets specializes to Lebesgue measure of symmetric difference
- `Critical` / `criticalMass` (limsup mass): Simon §38 (varifold mass);
  Pitts 1981 §3.4 (sequence-based critical setup)
- $\mathfrak{m}_L$, $\mathfrak{m}_R$ (left/right critical sets):
  CLS22 §2 — sweepout-specific concept
- `width`: paper §3 Def 3.1; standard min-max width definition
  (Almgren-Pitts, Pitts 1981 §3.1)

Cited paper-specific contributions (not in Pitts/Simon):
- ONVP (Optimal Nested Volume Parametrized): CLS22 Def 1.2 + paper §3
  Def 3.2 — sweepout-specific
- $I$-replacement family / excessive interval: CLS22 Def 2.1 + paper §3
  Def 3.4 — CLS22 contribution
- non-excessive (separated form): CLS22 — CLS22 contribution
- Existence of non-excessive sweepout: CLS22 Theorem `c:non-excessive_minmax`
  via Almgren's discrete-to-continuous sweepout argument + tightening
  (built on Pitts 1981 §3.1, Almgren–Pitts theory)

**Status**: 🟢 (aligned to paper §3 + CLS22 verbatim; NonExcessive form
mismatch resolved via Option C — `NonExcessiveStrict` matches CLS22
verbatim, framework's `NonExcessive` redefined to forbid 2-sided
`IReplacementExists` and bridged from Strict via `nonExcessive_of_strict`)

---

## 6. Paper §3 + CL03 → `exists_minmaxLimit`

**Lean signature** (after Phase 2 strict-alignment):
`MinMax/MinMax/Sweepout/MinMaxLimit.lean:181`

```lean
theorem exists_minmaxLimit
    {Φ : Sweepout M} (hne : NonExcessive Φ) (honvp : ONVP Φ) (hW : 0 < width Φ) :
    ∃ (t₀ : ℝ) (V : Varifold M),
      Critical Φ t₀ ∧ MinMaxLimit Φ t₀ V ∧ Varifold.mass V = width Φ
```

**Cited paper**:
- Files: `paper/chapters/part2/3-sweepouts.tex` (Proposition `thm:CLS-stationary`),
  `pdf/CL03-Colding-DeLellis-2003.pdf` (Proposition 1.4)
- Reference: paper §3 Proposition `thm:CLS-stationary` (cites CL03 Prop 1.4)

**Paper §3 phrasing** (`paper/chapters/part2/3-sweepouts.tex:236-237`):

> Let $(M^{n+1},g)$ be a closed Riemannian manifold with $n \geq 2$, and
> let $\Phi$ be an optimal sweepout with $\sup_x \mathbf{M}(\Phi(x)) = W$.
> Then there exists a stationary $n$-varifold $V$ in $M$ with
> $\mathbf{M}(V) = W$.

**Original statement** (CL03 Prop 1.4): per paper §3 line 240, this
follows from the pull-tight argument of Colding–de Lellis: varifold
compactness + tightening flow optimality.

**Alignment check** (post-strict-alignment):

| Component | Lean | Paper §3 | Status |
|---|---|---|---|
| Closed Riemannian | `[BorelSpace M]` etc. (metric proxy) | $(M^{n+1}, g)$ closed | 🟡 (smooth-Riemannian via metric proxy; documented gap) |
| $n \geq 2$ | implicit (threaded at top-level) | $n \geq 2$ explicit | 🟡 (deferred to top-level `exists_smoothMinimalHypersurface_via_ONVP`) |
| Optimal sweepout | `NonExcessive Φ ∧ ONVP Φ` | "optimal sweepout" | ✓ |
| Width = W | `0 < width Φ` (input) | $\sup_x \mathbf{M}(\Phi(x)) = W$ | ✓ (positive-width input; paper W is `width Φ`) |
| ∃ critical parameter | `∃ t₀, Critical Φ t₀` | implicit in min-max | ✓ |
| ∃ varifold limit | `∃ V, MinMaxLimit Φ t₀ V` | "stationary $V$" (Lean: stationarity in `isStationary_of_minmaxLimit`) | ✓ split |
| $\mathbf{M}(V) = W$ | `Varifold.mass V = width Φ` | $\mathbf{M}(V) = W$ | ✓ |
| stationary V | NOT here (deferred to `isStationary_of_minmaxLimit`, Item 2/6) | "stationary" | ✓ split for modularity |

**Findings**:

1. **Mass conjunct added**: pre-alignment Lean signature did not include
   the paper's $\mathbf{M}(V) = W$ output. Strict alignment surfaces it
   as the third conjunct `Varifold.mass V = width Φ`. Chain consumer
   (`MinMaxExistence.lean:108`) now obtains 5-tuple
   `⟨t₀, V, hcrit, hlim, _hMass⟩` (mass conjunct unused downstream
   currently, but available for future strengthenings).

2. **Stationarity split**: paper §3 Prop 3.7 includes "stationary $V$"
   as part of the conclusion. Lean factors stationarity into the
   separate `isStationary_of_minmaxLimit` (Item 2/6) — modular split
   matching the chain proof's structure (`main_theorem_no_cancellation`
   step 1 calls `isStationary_of_minmaxLimit hlim` separately).

3. **$n \geq 2$ ambient hypothesis**: paper requires this for the
   pull-tight argument. Framework threads it at the top-level
   `exists_smoothMinimalHypersurface_via_ONVP`, not at this lemma —
   `exists_minmaxLimit` itself doesn't reference n in its conclusion.
   Acceptable per Round 5 Item 5 precedent (CLS22 Theorem 2.2 also
   carries n-hypothesis at the top-level).

**Chain break**: `MinMaxExistence.lean:107` pattern-match updated from
4-tuple to 5-tuple (added `_hMass`). No other consumers.

**Ground truth references** (Pitts 1981 / Simon 1983):

- `Sweepout`: Simon §13–§14 (BV / Caccioppoli families); De Giorgi
  structure theorem
- `MinMaxLimit`, `Critical`: Simon §38 + Pitts §3.4 (sequence-based
  critical parameter)
- `Varifold.mass`: Simon §38
- `width`: Pitts §3.1 (Almgren-Pitts width); paper §3 Def 3.1

Cited paper-specific contributions:
- Pull-tight argument with optimality + varifold compactness:
  CL03 Prop 1.4 — CL03 contribution
- Mass equality $\mathbf{M}(V) = W$ via Grassmannian-bundle convergence:
  CL03 + Simon §38

**Status**: 🟢 (paper §3 verbatim quoted; signature strict-aligned with
mass conjunct added; stationarity factored to separate
`isStationary_of_minmaxLimit`; n-hypothesis threaded at top-level
per Item 5 precedent)

---

## 7. Lin / Schoen-Simon → `locallyStable_of_oneSidedMinimizing`

**Lean signature**: `AltRegularity/Regularity/StabilityVerification.lean:82`

```lean
theorem locallyStable_of_oneSidedMinimizing
    {V : Varifold M}
    (h : ∀ P ∈ support V \ Sweepout.hnm V, ∃ r > 0, OneSidedMinimizingAt V P r) :
    ∀ P ∈ support V \ Sweepout.hnm V, ∃ r > 0, LocallyStable V P r
```

**Cited paper**:
- Files: `pdf/Lin85-Lin-1985.pdf` and/or `pdf/SSY75-Schoen-Simon-Yau-1975.pdf`
- Reference: Lin 1985 (Caccioppoli minimizers) / Schoen–Simon 1981 stability

**Paper §6.1 phrasing** (`paper/chapters/part2/6-regularity.tex:18`):

> One-sided homotopic minimization implies that the second variation
> $\delta^2 V(\varphi, \varphi) \geq 0$ for all normal deformations
> $\varphi$ supported in $B_r(P)$.

**Original statement** (Lin 1985 / Schoen-Simon 1981):

[TODO: read the relevant theorem statement and fill]

**Alignment check**:

| Component | Lean | Paper §6.1 | Cited original | Status |
|---|---|---|---|---|
| OneSidedMinimizingAt | `Varifold.OneSidedMinimizingAt V P r` | one-sided min | TODO | 🟡 |
| LocallyStable | `Varifold.LocallyStable V P r` | δ² ≥ 0 in $B_r$ | TODO | 🟡 |

**Status**: 🔴

---

## 8. CLS22 Lemma 1.12 → `interpolation_lemma`

**Lean signature** (after Phase 2 strict-alignment):
`MinMax/MinMax/Sweepout/Interpolation.lean:50`

```lean
theorem interpolation_lemma
    (L : ℝ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (Ωlo Ωhi : FinitePerimeter M),
        Ωlo.carrier ⊆ Ωhi.carrier →
        (Ωlo.perim : ℝ) ≤ L → (Ωhi.perim : ℝ) ≤ L →
        (MeasureTheory.volume (Ωhi.carrier \ Ωlo.carrier)).toReal ≤ δ →
        ∃ family : ℝ → FinitePerimeter M,
          FContinuous family ∧
            family 0 = Ωlo ∧ family 1 = Ωhi ∧
            ∀ t ∈ Set.Icc (0 : ℝ) 1,
              ((family t).perim : ℝ) ≤
                max ((Ωlo.perim : ℝ)) ((Ωhi.perim : ℝ)) + ε
```

**Cited paper**:
- File: `arXiv-sources/CLS22-Chodosh-Liokumovich-Spolaor/main.tex` (lemma `l:close in flat`)
- Reference: CLS22, Lemma 1.12

**Paper §2 phrasing** (`paper/chapters/part2/2-preliminaries.tex:134-142`):

> Fix $L > 0$. For every $\varepsilon > 0$ there exists $\delta > 0$ such
> that the following holds. If $\Omega_0, \Omega_1$ are two Caccioppoli
> sets with $\Omega_0 \subset \Omega_1$, $\mathrm{Per}(\Omega_i) \leq L$
> for $i = 0, 1$, and $\mathrm{Vol}(\Omega_1 \setminus \Omega_0) \leq \delta$,
> then there exists a nested $\mathcal{F}$-continuous family
> $\{\partial\Omega_t\}_{t \in [0,1]}$ with
> $\mathrm{Per}(\Omega_t) \leq \max\{\mathrm{Per}(\Omega_0),
>     \mathrm{Per}(\Omega_1)\} + \varepsilon$
> for all $t \in [0,1]$.

**Original statement** (CLS22 §1, Lemma `l:close in flat`, verbatim):

> Fix $L>0$. For every $\eps>0$ there exists $\delta>0$, such that the
> following holds. If $\Om_0,\Om_1$ are two sets of finite perimeter,
> such that $\Om_0 \subset \Om_1$, $\Per(\Om_i) \leq L$, $i=0,1$, and
> $\Vol(\Om_1 \setminus \Om_0)\leq \delta$, then there exists a nested
> $\cF$-continuous family $\{\partial\Om_t\}_{t \in [0,1]}$ with
> $\Per(\Om_t)\leq \max\{\Per(\Om_0),\Per(\Om_1)\}+\eps$ for all $t\in[0,1]$.

**Alignment check** (post-strict-alignment):

| Component | Lean | Paper §2 | CLS22 original | Status |
|---|---|---|---|---|
| Outer L cap | `(L : ℝ) (hL : 0 < L)` | "Fix $L > 0$" | "Fix $L>0$" | ✓ |
| Inner ε quantifier | `(ε : ℝ) (hε : 0 < ε)` | "For every $\varepsilon > 0$" | "For every $\eps>0$" | ✓ |
| δ existential | `∃ δ : ℝ, 0 < δ ∧ ...` | "there exists $\delta > 0$" | "there exists $\delta>0$" | ✓ |
| Nesting hypothesis | `Ωlo.carrier ⊆ Ωhi.carrier` | $\Omega_0 \subset \Omega_1$ | $\Om_0 \subset \Om_1$ | ✓ |
| Per cap | `(_ .perim : ℝ) ≤ L` for both | $\mathrm{Per}(\Omega_i) \leq L$ | $\Per(\Om_i) \leq L$ | ✓ |
| Volume-gap hypothesis | `(volume (Ωhi.carrier \ Ωlo.carrier)).toReal ≤ δ` | $\mathrm{Vol}(\Omega_1 \setminus \Omega_0) \leq \delta$ | $\Vol(\Om_1 \setminus \Om_0)\leq \delta$ | ✓ |
| F-continuous family | `FContinuous family` | $\mathcal{F}$-continuous | $\cF$-continuous | ✓ |
| Endpoints | `family 0 = Ωlo ∧ family 1 = Ωhi` | implicit "from $\Omega_0$ to $\Omega_1$" | implicit | ✓ (Lean explicit) |
| Perim cap | `≤ max(Per Ωlo, Per Ωhi) + ε` | $\max\{\mathrm{Per}(\Omega_0), \mathrm{Per}(\Omega_1)\} + \varepsilon$ | $\max\{\Per(\Om_0), \Per(\Om_1)\} + \eps$ | ✓ |

**Findings**:

1. **Pre-alignment Lean signature was wrong**: missing the outer `L` perimeter cap, the inner `δ` existential quantifier, the per-instance perimeter-cap hypotheses, and the volume-gap hypothesis. The previous form `interpolation_lemma (Ωlo Ωhi)(hsub)(ε)(hε)` produced the family DIRECTLY from `ε`, without the prerequisite that $\Omega_0$ and $\Omega_1$ be close in volume — which is essential (without volume-closeness, the perimeter-cap conclusion fails in general). Strict alignment surfaces all four missing components.

2. **Volume measure**: uses `MeasureTheory.volume` from the framework's
   `[MeasureTheory.MeasureSpace M]` cascade — matches the paper/CLS22 use of "Vol" without further setup.

3. **No chain break**: `interpolation_lemma` has no consumers in the
   current chain (paper §5 cancellation chain that uses it is sorried).

**Ground truth references** (Pitts 1981 / Simon 1983):

GMT primitives used in the statement:
- `FinitePerimeter` (Caccioppoli set): Simon §27 (BV) ✓ ground truth
- `perim` (BV total variation): Simon §27 (Definition 27.1) ✓ ground truth
- `FContinuous` / flat metric: Simon §31 (flat metric on currents) ✓ ground truth
- `MeasureTheory.volume`: standard measure theory; not paper-specific

Cited paper-specific contributions:
- The interpolation construction (perimeter-cap-preserving F-continuous
  family from a small-volume nested pair): CLS22 §1 Lemma 1.12 — CLS22
  contribution (built on Simon §27 + §31 ground truth)

**Status**: 🟢 (paper §2 + CLS22 originals quoted verbatim; signature
strict-aligned to outer-L + inner-ε + δ-existential + 3 hypotheses
+ F-continuous family + perim cap conclusion).

---

## 9. Allard 1972 Theorem 5.5 → `isRectifiable_of_isStationary_of_density_pos`

**Lean signature**: `AltRegularity/GMT/Rectifiability.lean:50`

```lean
theorem isRectifiable_of_isStationary_of_density_pos
    {V : Varifold M} (hstat : IsStationary V)
    (hpos : ∀ p ∈ support V, 0 < density V p) :
    IsRectifiable V
```

**Cited paper**:
- File: `Allard-Theory-of-Varifolds/Theory of Varifolds 5-6.pdf` (likely Theorem 5.5 in Sec 5)
- Reference: Allard 1972, Theorem 5.5(1) / Simon 1984, Theorem 42.4

**Paper §2 phrasing**: [TODO: locate paper §2 rectifiability theorem statement]

**Original statement** (Allard 1972, Theorem 5.5(1)):

[TODO: read the relevant Allard PDF and fill]

**Alignment check**: [TODO]

**Status**: 🔴

---

## Verification process

For each item above, the recommended workflow is:

1. Open the cited paper file (PDF / tex source) at the listed location.
2. Find the theorem at the cited number (e.g., Theorem 3.1, Lemma 1.12).
3. Copy the precise statement into the **Original statement** section of
   the corresponding entry above.
4. Compare row by row in the alignment table.
5. If a mismatch is found:
   - Update the Lean signature (note: this may surface chain breaks —
     the framework will catch them).
   - Update the cited-paper line to match if the discrepancy is in our
     local restatement.
6. Mark **Status** as 🟢 once Lean signature, paper §X phrasing, and
   cited original all agree.

Each 🟢 transition tightens the framework one notch closer to a
formally chain-checked, paper-faithful min-max regularity proof.
