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

1. **Lean signature** is auto-extracted from current source (see file:line).
2. **Paper §X phrasing** (the paper's own restatement) is filled by
   reading `paper/chapters/part2/*.tex`.
3. **Cited original statement** is filled by reading the local PDF /
   arXiv source listed under "Cited paper file".
4. **Alignment check** compares each component (hypotheses + conclusion)
   row-by-row.
5. **Status** advances 🔴 → 🟡 (mismatch flagged) → 🟢 (verified aligned).

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

**Status**: 🟡 (paper §4 verified verbatim; cited original TODO)

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

**Lean signature**: `AltRegularity/Sweepout/HomotopicMinimization.lean:96`

```lean
theorem hnm_finite_of_nonExcessive
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hne : NonExcessive Φ) (hcrit : Critical Φ t₀)
    (hlim : MinMaxLimit Φ t₀ V) :
    (hnm V).Finite
```

**Cited paper**:
- File: `arXiv-sources/CLS22-Chodosh-Liokumovich-Spolaor/main.tex`
- Reference: Chodosh–Liokumovich–Spolaor (CLS22)
- Theorem: Proposition 3.1

**Paper §6.1 phrasing** (`paper/chapters/part2/6-regularity.tex:18` and `3-sweepouts.tex:451`):

> By [CLS22, Proposition 3.1], the set $\mathfrak{h}_{\mathrm{nm}}(V)$ of
> non-homotopic-minimizing points (Definition 3.8) is finite.

**Original statement** (CLS22, Proposition 3.1):

[TODO: read `CLS22-Chodosh-Liokumovich-Spolaor/main.tex` and fill]

**Alignment check**:

| Component | Lean | Paper §6.1 | Cited original | Status |
|---|---|---|---|---|
| NonExcessive Φ | `hne` | "non-excessive" | TODO | 🟡 |
| Critical Φ t₀ | `hcrit` | implicit | TODO | 🟡 |
| MinMaxLimit Φ t₀ V | `hlim` | min-max limit | TODO | 🟡 |
| hnm V definition | paper Def 3.8 / `Sweepout.hnm` | Def 2.5 | TODO | 🟡 |
| Conclusion | `(hnm V).Finite` | "finite" | TODO | 🟡 |

**Status**: 🔴

---

## 4. DLT 2013 Proposition A.1 → `dlt_criterion`

**Lean signature**: `AltRegularity/Integrality/PerimeterConvergence.lean:43`

```lean
theorem dlt_criterion
    {Φ : Sweepout M} {t₀ : ℝ} {V : Varifold M}
    (hlim : Sweepout.MinMaxLimit Φ t₀ V)
    (hWeak : Sweepout.DChiWeakConverge Φ t₀)
    (hPer : Sweepout.PerimeterConverge Φ t₀) :
    V = Varifold.ofBoundary (Φ.slice t₀)
```

**Cited paper**:
- File: `arXiv-sources/DLT13-DeLellis-Tasnady/DLT13-DeLellis-Tasnady.tex`
- Reference: De Lellis–Tasnady, "The existence of embedded minimal hypersurfaces", 2013
- Theorem: Proposition A.1

**Paper §6.1 phrasing**: [TODO: locate exact paper §6.1 line]

**Original statement** (DLT 2013, Proposition A.1):

[TODO: read `DLT13-DeLellis-Tasnady.tex` and fill]

**Alignment check**:

| Component | Lean | Paper | Cited original | Status |
|---|---|---|---|---|
| weak convergence | `DChiWeakConverge Φ t₀` (opaque) | TODO | TODO | 🔴 |
| perimeter convergence | `PerimeterConverge Φ t₀` | TODO | TODO | 🔴 |
| Conclusion | `V = ofBoundary (Φ.slice t₀)` | TODO | TODO | 🔴 |

**Status**: 🔴

---

## 5. CLS22 Theorem 2.2 → `exists_nonExcessive_ONVP`

**Lean signature**: `AltRegularity/Sweepout/NonExcessive.lean:145`

```lean
theorem exists_nonExcessive_ONVP (M : Type*)
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] :
    ∃ Φ : Sweepout M, NonExcessive Φ ∧ ONVP Φ ∧ 0 < width Φ
```

**Cited paper**:
- File: `arXiv-sources/CLS22-Chodosh-Liokumovich-Spolaor/main.tex`
- Reference: CLS22, Theorem 2.2

**Paper §3 phrasing** (`paper/chapters/part2/3-sweepouts.tex:230-232`):

> [Theorem~thm:non-excessive-existence] Let $(M^{n+1},g)$ be a closed
> Riemannian manifold with $2\leq n\leq 6$. There exists an (ONVP) sweepout
> $\Psi$ such that every $x\in \mathfrak{m}_L(\Psi)$ is not left excessive
> and every $x \in \mathfrak{m}_R(\Psi)$ is not right excessive.

**Original statement** (CLS22, Theorem 2.2):

[TODO: read `CLS22 main.tex` and fill]

**Alignment check**:

| Component | Lean | Paper §3 | Cited original | Status |
|---|---|---|---|---|
| dim hypothesis | `[CompactSpace M]` | $2 \le n \le 6$ | TODO | 🟡 |
| ONVP | `ONVP Φ` | "(ONVP) sweepout" | TODO | 🟡 |
| Non-excessive (one-sided form) | `NonExcessive Φ` (combined L+R) | $\mathfrak{m}_L$ not left + $\mathfrak{m}_R$ not right | TODO | 🟡 |
| Width > 0 | `0 < width Φ` | implicit | TODO | 🟡 |

**Hidden gap candidate**: paper §3 phrases non-excessive as a left/right separation; framework's `NonExcessive` is the unified `∀ t crit → ¬ Excessive`. Verify equivalence holds at the cited-paper level.

**Status**: 🔴

---

## 6. Paper §3 + CL03 → `exists_minmaxLimit`

**Lean signature**: `AltRegularity/Sweepout/MinMaxLimit.lean:122`

```lean
theorem exists_minmaxLimit
    {Φ : Sweepout M} (hne : NonExcessive Φ) (honvp : ONVP Φ) (hW : 0 < width Φ) :
    ∃ (t₀ : ℝ) (V : Varifold M), Critical Φ t₀ ∧ MinMaxLimit Φ t₀ V
```

**Cited paper**:
- Files: `paper/chapters/part2/3-sweepouts.tex`, `pdf/CL03-Colding-DeLellis-2003.pdf`
- Reference: paper Proposition 3.7 + CL03 Proposition 1.4

**Paper §3 phrasing**: [TODO: locate Proposition 3.7 statement]

**Original statement** (CL03, Proposition 1.4):

[TODO: read `CL03 PDF` and fill]

**Alignment check**: [TODO]

**Status**: 🔴

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

**Lean signature**: `AltRegularity/Sweepout/Interpolation.lean:25`

```lean
theorem interpolation_lemma
    (Ωlo Ωhi : FinitePerimeter M) (hsub : Ωlo.carrier ⊆ Ωhi.carrier)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ family : ℝ → FinitePerimeter M,
      FContinuous family ∧
        family 0 = Ωlo ∧ family 1 = Ωhi ∧
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ((family t).perim : ℝ) ≤ max ((Ωlo.perim : ℝ)) ((Ωhi.perim : ℝ)) + ε
```

**Cited paper**:
- File: `arXiv-sources/CLS22-Chodosh-Liokumovich-Spolaor/main.tex`
- Reference: CLS22, Lemma 1.12

**Original statement** (CLS22, Lemma 1.12):

[TODO: read `CLS22 main.tex` Lemma 1.12 and fill]

**Alignment check**: [TODO]

**Status**: 🔴

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
