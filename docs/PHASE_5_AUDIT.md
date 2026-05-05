# Phase 5 — CLAUDE.md 战略对齐审计

**日期**: 2026-04-28
**审计目的**: 用户战略指令「黎曼几何模块复用性极高、极其优秀的软件工程、至少达到 Mathlib 标准」与现行 CLAUDE.md 的对齐审计。
**Audit-only**: 不动 code，仅 propose CLAUDE.md edit。

---

## 用户战略指令拆解

「黎曼几何模块复用性极高、极其优秀的软件工程、至少达到 Mathlib 标准」三层语义：

1. **复用性极高** — Riemannian 模块是 first-class reusable lib，独立于 paper domain，可被任意下游 Lean 项目消费。
2. **极其优秀的软件工程** — 软件工程是 substantive deliverable，不是 cosmetic polish。
3. **至少达到 Mathlib 标准** — 用 Mathlib 作为 concrete quality benchmark；自我设限（self-impose）的 quality bar，不是 reactive 跟随。

战略含义：所有 technical default 是「Mathlib 怎么做我们怎么做」。Software engineering 是 first-class phase，不是 last-phase polish。

---

## 现行 CLAUDE.md 战略 framing 的优点

CLAUDE.md 当前在以下几个方面已经 align 良好：

### ✓ Self-build is the default action（line 43-75）

明确 declare framework 不等 Mathlib，自建是 default。这部分 fully align 用户指令的 "Mathlib 标准" — Mathlib 标准是 self-imposed，不是 reactive。

### ✓ Framework Stance vs Mathlib（line 204-235）

明确 declare：
- "Self-impose Mathlib standard, do not cater"
- "Mathlib is upstream, not pacemaker"
- "PR readiness is bonus, not motivation"

这三条 declare 已经把 Mathlib 标准定位为 self-imposed quality bar，与用户指令的 "至少达到 Mathlib 标准" 一致。

### ✓ Failure protocol（line 116-157）

明确拒绝 lazy retreat framings，拒绝 "specialized expertise required" / "multi-session work" 等借口。这段 align 用户的 "极其优秀的软件工程" — 不允许在质量上让步。

### ✓ Refactor Protocol（line 159-169）

强调 refactor 是 strategic re-audit，不是 implementation work。这与「持续达到 Mathlib 标准」一致 — 软件工程质量是 recurring ritual 而非 one-time event。

---

## Gap 识别

### Gap 1: Mission section 把 reusability 框定为 "Mathlib upstream candidates"（line 10）

**现状**:

> **Reusable Lean 4 mathematical software libraries**: GeometricMeasureTheory, MinMax theory, Regularity theory — Mathlib upstream candidates.

**问题**:
- "Mathlib upstream candidates" 把 reusability 的目标框定为「未来 PR 到 Mathlib」。
- 用户指令的核心是 **复用性本身**，PR 与否是次要的。复用性的 audience 包括下游研究者、其它 Lean 项目、教学使用，不只是 Mathlib upstream。
- Riemannian 模块在 line 22 中也被描述为 "future spin-out candidate as a standalone Lean library (Mathlib upstream / community use)" — 这里 community use 已经被提及，但 mission 顶部没有对应。

**严重程度**: Major（影响 strategic framing 的 first-class 表达）。

**建议修改**: Mission section 把 "Mathlib upstream candidates" 升级为 "reusable lib at Mathlib software engineering standard, with Mathlib upstream as one possible distribution channel"。强调 quality bar 而非 distribution path。

---

### Gap 2: Phase 5 被框定为 "UX optimization"（line 269）

**现状**:

> **Phase 5** (event-triggered): UX optimization on stabilized framework interface — `@[simp]`, `@[ext]`, `@[simps]`, `abbrev`, naming polish, API ergonomics.

**问题**:
- "UX optimization" 听起来像 cosmetic polish。
- 把 substantive software engineering work（typeclass 设计审计、API stability tier、deprecation policy、CI 验证、concrete instance、worked example、module docstring header、dependency 卫生）压缩成 "UX optimization"，与用户指令 "极其优秀的软件工程" 不匹配。
- 列举的内容（`@[simp]` / `@[ext]` / `@[simps]` / `abbrev`）只是软件工程标准的 attribute 层，没有覆盖 module structure / API surface / typeclass design / CI infra 等更宏观维度。

**严重程度**: Critical（直接影响 Phase 5 task 范围与执行心态）。

**建议修改**: Phase 5 从 "UX optimization" reframe 为 "Software Engineering to Mathlib Standard"，作为 substantive phase。任务清单从 attribute polish 升级为完整的 9 维度软件工程质量提升（详见 PHASE_5_PLAN.md）。

---

### Gap 3: CI / verification infrastructure 被推迟到 Phase 6（line 270）

**现状**:

> **Phase 6**: Final pre-release polish — CI, doc-gen4, README, references.bib, optional Mathlib upstream PR for stabilized lib subsets.

**问题**:
- CI 是 software engineering bedrock，不是 final-polish 内容。
- Mathlib 标准的 build verify / sorry counter / axiom audit 应该是 Phase 5 的核心，而不是 release 前的最后一步。
- Sorry discipline（CLAUDE.md line 179-190）已经 declare，但没有 enforcement mechanism — 这正是 CI 的工作。

**严重程度**: Major（影响 sorry discipline 与 chain proof 0-sorry 不变量的 enforcement）。

**建议修改**: 把 CI / sorry counter / axiom audit 从 Phase 6 提前到 Phase 5。Phase 6 留给 README / CITATION / LICENSE / 版本发布 / 可选 Mathlib PR。

---

### Gap 4: Standards section 缺 Mathlib 软件工程具体 practice（line 171-202）

**现状**: Standards section 包含 5 类：
- Paper-faithful grounding
- Sorry / opaque / placeholder discipline
- Chain proofs
- Ground truth annotation
- Naming（仅 namespace 级，concept-level not person-level）

**问题**: 这 5 类是 mathematical fidelity standards，**不是 software engineering standards**。具体缺失：

| Mathlib 软件工程 practice | 现状 |
|------------------------|------|
| Module-level docstring header（`/-! # ... -/`）作为 file-level requirement | 未声明 |
| `@[simp]` / `@[ext]` / `@[simps]` 标注政策 | 未声明 |
| `def` vs `noncomputable def` vs `abbrev` 选择规则 | 未声明 |
| `private` modifier 内部 helper 政策 | 未声明 |
| `class` vs `structure` 选择规则 | 未声明 |
| `extends` vs separate typeclass 选择规则 | 未声明 |
| Public API vs internal helper 区分（stability tier） | 未声明 |
| `@[deprecated]` 政策 | 未声明 |
| File-level import 卫生（DAG / 冗余 import） | 未声明 |
| Concrete instance 配套要求（每个 typeclass 至少一个 example instance） | 未声明 |
| Section variable 使用约定（数量上限、`omit` 用法） | 未声明 |

**严重程度**: Major（缺乏 explicit standard 导致 Claude Code 在执行时缺乏对齐基准）。

**建议修改**: Standards section 增加新 sub-section "Mathlib software engineering standard"（具体内容见 PHASE_5_PLAN.md 的 Mathlib standard reference 部分，引用至 CLAUDE.md）。

---

### Gap 5: UX Optimization Timing section 与 Phase 5 框定不一致（line 237-244）

**现状**:

> UX optimizations (`@[simp]` / `@[ext]` / `@[simps]` / `abbrev` / naming polish / API ergonomics) require stable interfaces. Apply only when:
> - Framework self-build primitive set has stabilized (no further additions or signature changes expected),
> - Concepts are settled mathematically and no further refactor is planned.
>
> Premature UX optimization on evolving interfaces wastes work — polish gets discarded when refactor changes signatures. Defer to *event-triggered* timing: typically after refactor consolidation or before `v1.0` release. Phase 5 / Phase 6 work, not now.

**问题**:
- 这一段把 software engineering 全部归为 "UX optimization"，强化了 Phase 5 = cosmetic 的误解。
- 实际上软件工程的部分内容（module docstring header、CI、private modifier、import 卫生）**不要求 interface 稳定**，可以在任何时候推进。
- `@[simp]` 标注与 typeclass field 调整确实需要 interface 稳定，但这只是软件工程的一部分。

**严重程度**: Major（强化了错误的 Phase 5 framing）。

**建议修改**: 把 "UX Optimization Timing" 拆为两层：
1. **Interface-stable optimizations**（要求 interface 稳定才推进）：`@[simp]` / `@[ext]` / `@[simps]` / `abbrev` / typeclass field 重组。
2. **Interface-agnostic engineering**（任何时候都可以推进）：module docstring header / CI / import 卫生 / private modifier / docstring 完整性 / concrete instance 配套。

后者归 Phase 5 的 always-on 子项；前者归 Phase 5 的 event-triggered 子项（在 Riemannian interface 稳定的当下，时机已到）。

---

## 提议的 CLAUDE.md edit

下面给出具体的 before/after 修改建议。每条独立，可单独 apply。

---

### Edit 1: Mission section（line 10）

**Before**:

```markdown
2. **Reusable Lean 4 mathematical software libraries**: GeometricMeasureTheory, MinMax theory, Regularity theory — Mathlib upstream candidates.
```

**After**:

```markdown
2. **Reusable Lean 4 mathematical software libraries** at Mathlib software engineering standard: Riemannian, GeometricMeasureTheory, MinMax, Regularity. Reusability and Mathlib-grade software engineering are first-class quality bars — Mathlib upstream PR is one possible distribution channel, not the goal itself. Audience includes downstream research groups, other Lean projects, and graduate-course teaching use.
```

**Rationale**: 把 reusability 的 audience 与质量标准 explicit 化，避免被解读为「未来 PR 到 Mathlib 才有意义」。

---

### Edit 2: Phase Plan — Phase 5 reframe（line 269）

**Before**:

```markdown
- **Phase 5** (event-triggered): UX optimization on stabilized framework interface — `@[simp]`, `@[ext]`, `@[simps]`, `abbrev`, naming polish, API ergonomics.
```

**After**:

```markdown
- **Phase 5** (current): Software engineering to Mathlib standard. Substantive phase covering module structure (docstring header, namespace, import order, section variable hygiene), API surface (public/internal split via `private`, stability tier, `@[deprecated]` policy), typeclass design audit (field count, axiomatic vs derived, inheritance depth), definition style (`def` vs `noncomputable def` vs `abbrev` rules, `class` vs `structure`), theorem/lemma annotation (`@[simp]` / `@[ext]` / `@[simps]` policy), docstring completeness, concrete instance scaffolding (each typeclass has ≥1 example instance), dependency hygiene (DAG check, redundant import removal), CI infrastructure (build verify, sorry counter, axiom audit binary), worked-example files. Riemannian module is the first target (interface stable post-Phase 4.7); GMT/MinMax/Regularity follow.
```

**Rationale**: Phase 5 升级为 substantive software engineering phase。明确 9 个维度的工作内容，对齐 Mathlib 标准。

---

### Edit 3: Phase Plan — Phase 6 narrowing（line 270）

**Before**:

```markdown
- **Phase 6**: Final pre-release polish — CI, doc-gen4, README, references.bib, optional Mathlib upstream PR for stabilized lib subsets.
```

**After**:

```markdown
- **Phase 6**: Pre-release packaging — README, CITATION.cff, LICENSE, CHANGELOG, doc-gen4 HTML output, version tagging, optional Mathlib upstream PR for stabilized lib subsets. (CI / sorry counter / axiom audit moved to Phase 5 as software engineering bedrock, not release polish.)
```

**Rationale**: CI 是 Phase 5 的 enforcement mechanism，不是 release-time 内容。Phase 6 留给真正 release 相关的 packaging 工作。

---

### Edit 4: Standards section — 新增 Mathlib software engineering subsection（在 line 200 "Naming" 之后）

**Before** (line 200-202):

```markdown
### Naming

Namespace and package names are concept-level, not person-level. Avoid attribution names (no `Wickramasekera`, no `AlmgrenPitts` as top-level package). People appear in citations + docstrings, not in namespace structure.
```

**After** (in addition to the existing Naming subsection, append a new subsection):

```markdown
### Naming

Namespace and package names are concept-level, not person-level. Avoid attribution names (no `Wickramasekera`, no `AlmgrenPitts` as top-level package). People appear in citations + docstrings, not in namespace structure.

Theorem/lemma names follow Mathlib's subject_verb_object pattern (`koszul_smul_right`, `metricInner_self_pos`). Definition names are descriptive concept-level (`leviCivitaConnection`, `secondFundamentalFormScalar`).

### Mathlib software engineering standard

Framework adopts Mathlib's specific software engineering practices as the self-imposed quality bar. Concrete rules:

**Module structure**:
- Every `.lean` file opens with `/-! # Title\n\nDescription...\n-/` module docstring before imports (Mathlib convention; see `Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean`).
- Imports ordered: external Mathlib → framework dependencies → local relative.
- One primary namespace per file, sub-namespaces ≤ 2 levels deep.
- `variable` declarations grouped at section top; use `omit ... in` for selective unbinding rather than over-broad section variables.

**Definition style**:
- `def` for computable; `noncomputable def` for definitions using `Classical.choose` / non-constructive existence; `abbrev` only for transparent type aliases.
- `class` for typeclass-resolution targets; `structure` for plain data; flat `def` for non-bundled functions.
- Existence theorems prefer named definitions (via `Classical.choose`) over raw `∃`-stated theorems when the value is consumed downstream.

**Theorem/lemma annotation**:
- `@[simp]` only on lemmas that are confluent under simp normal form (no recursion, target is canonical). Never on sorry'd statements.
- `@[ext]` on extensionality lemmas for structures/classes.
- `@[simps]` on structure/class definitions whose fields users will access.
- `private` for internal helpers not part of public API. Public lemmas/definitions have docstrings.

**Docstring requirement**:
- Every public definition/theorem has a docstring explaining mathematical content and citation (`**Ground truth**: ...`).
- Every typeclass has a docstring explaining design rationale (why `class` vs `structure`, what fields are axiomatic).
- Proof outlines as `--` comments for non-trivial proofs.

**Typeclass design**:
- Field count ≤ 5; if more, split into `extends`-chained sub-typeclasses.
- Axiomatic fields (raw assumptions) minimized; derived properties as separate theorems.
- No typeclass inheritance diamonds; explicitly document any `letI`-based local resolution.

**API surface**:
- Public API surface declared in module docstring (named identifiers).
- `@[deprecated]` annotation when API is replaced; redirect to replacement in deprecation message.
- PRE-PAPER stubs / sorry'd theorems carry `**Sorry status**: ...` docstring with repair plan (matches existing CLAUDE.md sorry discipline).

**Dependency hygiene**:
- File-level import DAG (no cycles); CI checks via `lake build`.
- Avoid redundant imports (e.g., `import A` and `import B` when `B` already imports `A`).
- Each module compilable in isolation when possible (clear dependency boundary).

**Concrete instance scaffolding**:
- Each typeclass has ≥1 concrete instance demonstrating usage (Mathlib pattern: `EuclideanSpace`, `Real.sphere`, etc.).
- Each substantive abstract definition has a `worked example` showing application on a non-trivial concrete case.

**CI infrastructure**:
- `lake build` passes on every commit.
- Sorry counter: a script enumerating all `sorry` occurrences with PRE-PAPER / CITED-BLACK-BOX / PAPER-INTERNAL / CONJECTURAL classification.
- Axiom audit: enumerate all `axiom` declarations + their repair plans.
- Both surfaced via CI workflow (`.github/workflows/ci.yml`).

**Section variables**:
- Per-section `variable` blocks ≤ 8 typeclass parameters; if more, split section.
- `omit` for selective unbinding (Mathlib pattern; see warnings about unused section variables).
```

**Rationale**: 把 9 维度的 Mathlib software engineering practice explicit 化，作为 Claude Code 执行时的对齐基准。具体规则替代抽象原则。

---

### Edit 5: UX Optimization Timing section — 拆分两层（line 237-244）

**Before**:

```markdown
## UX Optimization Timing

UX optimizations (`@[simp]` / `@[ext]` / `@[simps]` / `abbrev` / naming polish / API ergonomics) require stable interfaces. Apply only when:

- Framework self-build primitive set has stabilized (no further additions or signature changes expected),
- Concepts are settled mathematically and no further refactor is planned.

Premature UX optimization on evolving interfaces wastes work — polish gets discarded when refactor changes signatures. Defer to *event-triggered* timing: typically after refactor consolidation or before `v1.0` release. Phase 5 / Phase 6 work, not now.
```

**After**:

```markdown
## Software Engineering Timing

Two-tier timing rule:

### Interface-agnostic engineering (always-on)

These can advance at any time, regardless of interface stability:
- Module docstring headers
- `private` modifier on internal helpers
- Import DAG hygiene (remove redundant imports)
- Docstring completeness
- Section variable cleanup (`omit` declarations)
- Concrete instance scaffolding (when interface itself is stable for the typeclass in question)
- CI infrastructure (build verify, sorry counter, axiom audit)
- README / CHANGELOG / LICENSE / CITATION (documentation artifacts)

### Interface-stable optimizations (event-triggered)

Apply only when the relevant interface has stabilized:
- `@[simp]` / `@[ext]` / `@[simps]` annotation policy
- `abbrev` introduction
- Typeclass field reorganization
- Naming polish that breaks downstream signatures

The trigger is "no further additions or signature changes expected for the lib subset". Premature optimization on evolving interfaces wastes work. Riemannian post-Phase 4.7 is at this trigger point; GMT/MinMax/Regularity await Phase 2/3 stabilization.
```

**Rationale**: 把 software engineering 的 always-on 部分从 event-triggered constraint 解放出来，让 Phase 5 立即可推进 module structure / CI / docstring / private modifier 等工作。

---

## 总结

CLAUDE.md 现行 framing 在 self-build / Mathlib stance / failure protocol 等核心战略层面已经 align 用户指令。但在具体的 Mission framing、Phase Plan、Standards section 三个 surface 层面，存在 5 个具体 gap：

| Gap | 严重度 | 修改 section |
|-----|-------|------------|
| 1. Mission 把 reusability 框定为 Mathlib upstream candidates | Major | Mission（line 10） |
| 2. Phase 5 框定为 UX optimization | Critical | Phase Plan（line 269） |
| 3. CI 推迟到 Phase 6 | Major | Phase Plan（line 270） |
| 4. Standards 缺 Mathlib SE practice | Major | Standards（line 200 后新增） |
| 5. UX Optimization Timing 强化错误 framing | Major | UX Optimization Timing（line 237-244） |

5 条 edit 都是 explicit 的 before/after 修改，可以独立或一起 apply。建议作为一个 atomic CLAUDE.md edit commit。

修改后 CLAUDE.md 与用户指令对齐，PHASE_5_PLAN.md 的执行有了明确的 standard reference。
