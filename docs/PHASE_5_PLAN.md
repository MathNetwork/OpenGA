# Phase 5 — 软件工程到 Mathlib 标准 (执行计划)

**日期**: 2026-04-28
**目标**: 把 Riemannian 模块（以及未来 GMT / MinMax / Regularity）的软件工程质量提升到 Mathlib 标准，使框架成为复用性极高、可独立 spin-out 为 Lean 社区库的高质量软件工程产物。
**Plan-only**: 不动 code，待 user review 后转 sub-phase prompt 顺序执行。

---

## 0. Phase 5 战略定位

Phase 5 不是 cosmetic polish。它是 substantive software engineering phase，把 Mathlib 的 9 维度软件工程标准（module structure / definition style / theorem annotation / docstring / typeclass design / API surface / dependency hygiene / worked example / CI infra）逐一对齐落实。

执行顺序：先 Riemannian（interface 已经稳定，Phase 4.7 完成），再 GMT / MinMax / Regularity（待对应 phase 完成后跟进）。

---

## 1. Mathlib 软件工程标准参考

下述 9 维度作为 Phase 5 的 alignment baseline。每条 cite Mathlib 具体文件作为 reference standard。

### 1.1 模块结构 (Module structure)

**Mathlib 标准**:
- 文件首行（在 import 之前）的 `/-! # Title\n\nDescription...\n-/` module-level docstring。Reference: `Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean` 第 1-50 行。
- 单一主 namespace per file；sub-namespace ≤ 2 层。
- Import 顺序: 外部 Mathlib → 框架内部 → 本地相对。
- `variable` 在 section 顶部统一声明；用 `omit ... in` selective unbinding 而不是过宽的 section variable。

### 1.2 定义风格 (Definition style)

**Mathlib 标准**:
- `def`：可计算定义。
- `noncomputable def`：使用 `Classical.choose` / 非构造性存在的定义。
- `abbrev`：仅用于 transparent type alias（Mathlib 用法：`EuclideanSpace`、`Module.Free`）。
- `class`：typeclass 解析目标；`structure`：plain data；flat `def`：非 bundle 的函数。Reference: `RiemannianMetric` typeclass（OpenGALib 自身已 align）。
- 存在性定理：当值会被下游消费，优先 named def via `Classical.choose`，而不是 raw `∃`-stated theorem。

### 1.3 定理/引理标注 (Theorem/lemma annotation)

**Mathlib 标准**:
- `@[simp]`：仅在 confluent under simp normal form 的引理上。**绝不在 sorry'd 定理上标注**（违反 soundness）。
- `@[ext]`：structure / class 的 extensionality lemma。
- `@[simps]`：structure / class 定义上，自动生成 field accessor 的 simp lemma。
- `private`：内部 helper，不暴露为 public API。
- 命名：subject_verb_object pattern（`koszul_smul_right`, `ricci_symm`）。
- 假设顺序：typeclass / instance 在前，再 explicit hypothesis；同类型 hypothesis 按 dependency 顺序。

### 1.4 Docstring 要求 (Docstring)

**Mathlib 标准**:
- Module-level docstring（`/-! # Title -/`）含 keywords、high-level overview、definition/theorem groups。Reference: `Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean` 第 12-40 行（详细阐述 typeclass 设计与 diamond 问题）。
- 每个 public def/theorem 含 docstring（数学公式 + 引用）。
- 复杂证明含 `--` proof outline 注释。
- 教学性内容（推导、数学背景）放在 docstring 或 `/-! ## Section -/`，不另开 separate doc。

### 1.5 Typeclass 设计 (Typeclass design)

**Mathlib 标准**:
- Field 数量 ≤ 5；超出则用 `extends` 拆分。
- Axiomatic fields 最小化；derived properties 作为单独 theorem。
- 继承层级 ≤ 3 层；避免 diamond。
- `IsContMDiffRiemannianBundle` 是 reference example：单一公理 `exists_contMDiff`（Reference: `Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean` 第 66-70 行）。

### 1.6 API surface 稳定性

**Mathlib 标准**:
- Public API 在 module docstring 中 explicit 列出。
- `private` 标注 internal helpers。
- `@[deprecated "use X instead"]` 标注被替代 API。
- Stability tier 通过 namespace 区分（`Mathlib.Topology` vs `Mathlib.Topology.Algebra` 等）。

### 1.7 依赖卫生 (Dependency hygiene)

**Mathlib 标准**:
- File import DAG 无循环（CI enforce via `lake build`）。
- 无冗余 import（若 `A imports B` 且 `B imports C`，`A` 不应再 explicit import `C` 除非有特殊原因）。
- 每个 module 尽可能 compilable in isolation。

### 1.8 Worked example / Concrete instance

**Mathlib 标准**:
- 每个抽象 typeclass 有 ≥1 concrete instance。Reference: `Mathlib/Geometry/Manifold/VectorBundle/Riemannian.lean` 第 94-108 行的 Trivial bundle instance。
- 每个 substantive 定义有 worked example（`EuclideanSpace n`、`Real.sphere`）。
- `examples/` 目录或 `UXTest` section 演示 typeclass cascade 正确性。

### 1.9 CI / 验证基础设施

**Mathlib 标准**:
- `lake build` per commit。
- `#print axioms <theorem>` regression guard（Mathlib 用 `#guard_msgs` 的模式）。
- Sorry counter / axiom audit 自动化（comb_arg reference: `lake exe combarg-audit` 定义在 `Audit.lean`，参见 `docs/SOFTWARE_QUALITY_AUDIT.md`）。
- doc-gen4 HTML 输出。

---

## 2. Riemannian 模块 gap 审计 (按 9 维度)

下述审计 cite 具体行号 + 严重程度。审计来源: 本 Phase 5 audit pass + 已有的 `docs/SOFTWARE_QUALITY_AUDIT.md` (comb_arg vs OpenGALib)。

### Gap 表 (Riemannian 模块)

| 维度 | 文件 | 状态 | Specific gap | 严重度 |
|------|------|------|------------|-------|
| **1. 模块结构** | `Curvature.lean`、`Gradient.lean`、`SecondFundamentalForm.lean` | FAIL | 缺 `/-! # ... -/` module-level docstring header（直接从 import 开始） | Major |
| **1. 模块结构** | `Connection.lean` | PARTIAL | line 48-52 `variable` 块过大（8 个约束）；后续 6 处 `omit ... in` 选择性解绑，可读性受损 | Minor |
| **1. 模块结构** | `BumpFunction.lean` | PARTIAL | `open` 语句分散在 line 49 / 51-52，未在文件顶部统一声明 | Minor |
| **2. 定义风格** | 全部 | PASS | `noncomputable def` 标注规范；typeclass 用 `class`；abbrev 仅用于透明别名 | — |
| **3. 定理标注** | `Curvature.lean:98-100` | FAIL | `ricci_symm` 标注 `@[simp]` 但证明是 `sorry` — 违反 Mathlib soundness 原则 | **Critical** |
| **3. 定理标注** | `SecondFundamentalForm.lean:75` | PARTIAL | `secondFundamentalFormSqNorm_nonneg` 标注 `@[simp]` 在 sum-of-squares 上过度激进 | Minor |
| **3. 定理标注** | `Connection.lean:1004` | PARTIAL | `covDeriv` 无 docstring 且无 `private` 标记，但实际为 internal helper | Major |
| **4. Docstring** | `Curvature.lean:69-70` | PARTIAL | `ricciTraceMap` 的 `map_add'` / `map_smul'` sorry 无具体 repair plan 链接 | Minor |
| **4. Docstring** | 顶级（Riemannian/） | FAIL | 无 module facade 文件（如 `Riemannian.lean` 顶级 re-export + module docstring） | Major |
| **5. Typeclass 设计** | `Metric.lean:82` `RiemannianMetric` | PASS | 4 个 axiomatic fields；最小化设计；无继承钻石 | — |
| **6. API surface** | 全部 | FAIL | 无 module docstring 中的 public API 列表；无 stability tier 标注；无 `@[deprecated]` 政策 | Major |
| **6. API surface** | `Connection.lean:1004` `covDeriv` | FAIL | 暴露为 public，但实际是 internal helper（同上） | Major |
| **6. API surface** | `Metric.lean:104-108` `metricInnerRaw` | PARTIAL | 命名含 "Raw"，无 docstring 说明何时用它 vs `metricInner` | Minor |
| **7. 依赖卫生** | `Gradient.lean`、`SecondFundamentalForm.lean` | PARTIAL | 同时 import `Connection` 和 `Metric`，但 Connection 已 import Metric，造成冗余 | Minor |
| **7. 依赖卫生** | 全部 | PASS | 无循环依赖；DAG 清晰：`Metric → Connection → {Curvature, Gradient, SFF}` | — |
| **8. Concrete instance** | 全部 | FAIL | 无 EuclideanSpace 上的 `RiemannianMetric` instance；无 worked example 演示 typeclass cascade | Major |
| **8. Concrete instance** | `Gradient.lean`、`SecondFundamentalForm.lean` | FAIL | 无 UXTest section / example | Minor |
| **8. Concrete instance** | `BumpFunction.lean:262` 末尾 | PARTIAL | `extendVectorField` 无 UX test 验证平滑性 | Minor |
| **9. CI / 验证** | 仓库根 | FAIL | 无 `.github/workflows/ci.yml`；无 `lake exe ...-audit` binary；无 sorry counter 脚本 | Major |
| **9. CI / 验证** | 全部 | FAIL | 全局 axiom registry 缺失（已有 2 个 axiom: `tangentBundle_symmL_smoothAt`, `koszulLeviCivita_exists`，未集中追踪） | Major |

### Critical / Major gap 汇总

🔴 **Critical**:
- `Curvature.lean:98-100` `ricci_symm` 标注 `@[simp]` 但是 `sorry` — 立即修复

🟠 **Major**:
- `Curvature.lean` / `Gradient.lean` / `SecondFundamentalForm.lean` 缺 module docstring header
- `Connection.lean:1004` `covDeriv` 缺文档与 `private` 标记
- 无 Riemannian 顶级 facade 文件
- 无 EuclideanSpace 上的 `RiemannianMetric` concrete instance
- 无 CI 配置 / sorry counter / axiom audit binary
- 无全局 axiom registry

🟡 **Minor**:
- `Connection.lean:48-52` variable 块过大
- `BumpFunction.lean` open 语句分散
- `Gradient.lean` / `SecondFundamentalForm.lean` 冗余 import
- `metricInnerRaw` 缺使用指南
- `BumpFunction.lean` 末尾 UX test 不完整

---

## 3. Sequential 执行计划

下述 sub-phase 按三轨制排序：**Track 0 (Critical hot-fix) → Track A (结构) → Track B (验证基础设施) → Track C (Convention)**。每个 sub-phase 是 atomic commit boundary，build verify checkpoint 独立。

不做 LOC estimate，不做 time estimate。按结构优先、convention 后做的逻辑顺序排列。

---

## Track 0 — Critical hot-fix

### Phase 5.0 — Critical fix: `ricci_symm` `@[simp]` 标注

**任务**:
- 文件: `Riemannian/Curvature.lean`
- 修改 line 98 的 `@[simp]` 标注：要么补齐证明，要么移除 `@[simp]`。
- 鉴于 `ricci_symm` 的证明依赖 algebraic Bianchi identity（PRE-PAPER），先移除 `@[simp]`，留 sorry + 标注 `**Sorry status**: PRE-PAPER`。
- 增加 docstring 中的 repair plan link。

**Atomic commit**: 单文件修改，单 commit。
**Build verify**: `lake build Riemannian.Curvature`。
**关闭的 Mathlib standard**: 维度 3（定理标注）的 critical violation。
**关闭的 gap**: `Curvature.lean:98-100`。

---

## Track A — 结构性优化

### Phase 5.1 — Module docstring header for missing files

**任务**:
- `Riemannian/Curvature.lean` 顶部加 `/-! # Riemannian.Curvature ... -/` module docstring（仿照 `Connection.lean` 第 10-41 行的格式）。
- `Riemannian/Gradient.lean` 顶部加 module docstring。
- `Riemannian/SecondFundamentalForm.lean` 顶部加 module docstring（已有简短 docstring 在 line 4-30，但未在 import 前；需调整顺序）。

**Atomic commit**: 3 文件修改，单 commit。
**Build verify**: `lake build Riemannian`。
**关闭的 Mathlib standard**: 维度 1（模块结构）。
**关闭的 gap**: 3 个文件的 missing module docstring。

---

### Phase 5.2 — `private` 标注与 covDeriv 文档化

**任务**:
- `Connection.lean:1004` `covDeriv`：要么标记 `private`（如果完全是 internal），要么补充 docstring + 公开 API 注解。审计 `covDeriv` 的实际用途：在 Connection.lean 内部用于 `leviCivitaConnection`，未跨文件被 import。结论：标记 `private`。
- 全 Riemannian 模块审计内部 helper 是否需要 `private`（具体 candidates：`koszul_*` 内部辅助 `directionalDeriv_*` 系列已经是 `private`，无需修改）。

**Atomic commit**: Connection.lean 单文件修改，单 commit。
**Build verify**: `lake build` 全项目（确认无跨文件破坏）。
**关闭的 Mathlib standard**: 维度 6（API surface）。
**关闭的 gap**: `Connection.lean:1004` covDeriv 标记。

---

### Phase 5.3 — 冗余 import 清理 + variable 块拆分

**任务**:
- `Gradient.lean`、`SecondFundamentalForm.lean`：移除冗余的 `import Riemannian.Metric`（保留 `import Riemannian.Connection`，后者已 transitively import Metric）。
- `Connection.lean:48-52`：审计 variable 块。如果 8 个约束的合理性不足，拆为多个 sub-section（基础几何在 section A，Riemannian 加 metric 在 section B）。
- `BumpFunction.lean`：把分散的 `open` 语句聚集到文件顶部。

**Atomic commit**: 3 文件修改，单 commit。
**Build verify**: `lake build`。
**关闭的 Mathlib standard**: 维度 1（模块结构）+ 维度 7（依赖卫生）。
**关闭的 gap**: `Gradient.lean` / `SecondFundamentalForm.lean` 冗余 import + Connection.lean variable 块 + BumpFunction.lean open 散布。

---

### Phase 5.4 — Riemannian 顶级 facade 文件

**任务**:
- 新建 `Riemannian.lean` 文件作为顶级 facade（在 `Riemannian/` 目录之外，作为 lib entry point）。
- Module docstring 列出 public API:
  - `RiemannianMetric` typeclass（Metric.lean）
  - `metricInner`, `metricRiesz`, `metricInner_eq_iff_eq`（Metric.lean）
  - `koszulFunctional`, `koszulCovDeriv`, `leviCivitaConnection`（Connection.lean）
  - `riemannCurvature`, `ricci`, `scalarCurvature`（Curvature.lean）
  - `secondFundamentalFormScalar`, `secondFundamentalFormSqNorm`, `meanCurvature`（SecondFundamentalForm.lean）
  - `manifoldGradient`, `manifoldGradientNormSq`（Gradient.lean）
  - `BumpFunction.*`（BumpFunction.lean）
- Re-export 所有 public 名字。

**Atomic commit**: 新增 `Riemannian.lean`，更新 `lakefile.lean` 入口（如果需要）。
**Build verify**: `lake build Riemannian`。
**关闭的 Mathlib standard**: 维度 4（docstring）+ 维度 6（API surface 中的 public API 列表）。
**关闭的 gap**: 无 Riemannian 顶级 facade。

---

### Phase 5.5 — Concrete instance 配套：EuclideanSpace 上的 RiemannianMetric

**任务**:
- 新建 `Riemannian/Examples/EuclideanSpace.lean`（或在 `Metric.lean` 末尾的新 section）。
- 提供 `instance riemannianMetricEuclideanSpace : RiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (EuclideanSpace ℝ (Fin n))` 通过 standard inner product 提供 metric tensor。
- `worked example` 演示在 `EuclideanSpace ℝ (Fin n)` 上：
  - `metricInner` 计算
  - `metricRiesz` 与 standard Riesz 对应
  - `manifoldGradient` 对 `f(x) = ‖x‖²` 的具体值
- 或者用更简单的 `M = ℝ` (1-d EuclideanSpace) 作为 minimal worked example。

**Atomic commit**: 新文件 + lakefile 更新。
**Build verify**: `lake build Riemannian.Examples.EuclideanSpace`。
**关闭的 Mathlib standard**: 维度 8（concrete instance / worked example）。
**关闭的 gap**: 无 EuclideanSpace 上 `RiemannianMetric` instance；无 worked example。

**⚠️ 战略决策点**: 用户需要 review 是用 `EuclideanSpace ℝ (Fin n)` 还是更简单的 `ℝ` 作为 minimal example。`EuclideanSpace ℝ (Fin n)` 更接近 Mathlib 标准（covers higher-dim case），`ℝ` 更简单。建议 `EuclideanSpace ℝ (Fin n)`。

---

### Phase 5.6 — UXTest 补全

**任务**:
- `Gradient.lean` 末尾添加 UXTest section，验证 `manifoldGradient` + `metricRiesz` 可用。
- `SecondFundamentalForm.lean` 末尾添加 UXTest section，验证 `secondFundamentalFormScalar` + `meanCurvature` typeclass cascade。
- `BumpFunction.lean:262` 后补完 `extendVectorField` UX test。

**Atomic commit**: 3 文件修改，单 commit。
**Build verify**: `lake build`。
**关闭的 Mathlib standard**: 维度 8（concrete instance / worked example）的 UXTest 部分。
**关闭的 gap**: Gradient / SecondFundamentalForm / BumpFunction UXTest 缺失。

---

### Phase 5.7 — Riemannian standalone-able audit

**任务**:
- 验证 Riemannian 模块可以从 OpenGALib 中独立 spin out 为 standalone Lean lib。
- 检查 import 是否仅依赖 Mathlib（不依赖 GMT / MinMax / Regularity）。
- 验证 namespace 不引用 paper-specific 概念。
- 如果通过，记录在 `docs/RIEMANNIAN_STANDALONE.md`：列出 spin-out 步骤（`Riemannian/` → 单独 git repo + lakefile）。
- 此为 Track A 的收尾 audit，验证结构稳定性。

**Atomic commit**: `docs/RIEMANNIAN_STANDALONE.md` 单文件，单 commit。
**Build verify**: 无 code 影响（纯 doc）。
**关闭的 Mathlib standard**: 用户指令的 "复用性极高"。
**关闭的 gap**: 无 standalone 验证。

---

## Track B — 验证基础设施

### Phase 5.8 — Axiom registry + sorry catalog

**任务**:
- 新建 `docs/AXIOM_STATUS.md`：列出框架所有 `axiom` 声明 + 每个的 repair plan + 优先级。
  - 当前列表：
    - `Riemannian/Metric.lean:421` `tangentBundle_symmL_smoothAt`（Phase 4.8）
    - `Riemannian/Connection.lean:879` `koszulLeviCivita_exists`（Phase 4.7.8.C）
- 新建 `docs/SORRY_CATALOG.md`：列出框架所有 `sorry` 出现位置 + 分类（PRE-PAPER / CITED-BLACK-BOX / PAPER-INTERNAL / CONJECTURAL）+ repair plan。
  - 当前 Riemannian 中的 sorry:
    - `Riemannian/Curvature.lean:69` `ricciTraceMap.map_add'` (PRE-PAPER)
    - `Riemannian/Curvature.lean:70` `ricciTraceMap.map_smul'` (PRE-PAPER)
    - `Riemannian/Curvature.lean:100` `ricci_symm` (PRE-PAPER, blocked by Bianchi)
- 用 Lean script 或 shell grep 自动生成（可选 future improvement）。

**Atomic commit**: 2 个 markdown 文件，单 commit。
**Build verify**: 无 build 影响（纯 doc）。
**关闭的 Mathlib standard**: 维度 9（CI / 验证）的 axiom audit / sorry counter。
**关闭的 gap**: 全局 axiom registry 缺失；sorry 无中央追踪。

---

### Phase 5.9 — CI workflow

**任务**:
- 新建 `.github/workflows/ci.yml`，参照 comb_arg 的格式（见 `docs/SOFTWARE_QUALITY_AUDIT.md` 第 60-62 行）：
  - `lake build` 全 lib
  - `grep -rn "sorry" Riemannian/ ...` snapshot 当前 sorry 数量，对比 `docs/SORRY_CATALOG.md` 已知列表，若 mismatch 则 fail
  - `grep -rn "^axiom" Riemannian/ ...` snapshot 当前 axiom 数量，对比 `docs/AXIOM_STATUS.md`，若 mismatch 则 fail
- （可选）新建 `lake exe opengalib-audit` binary 实现上述检查 in Lean，更精确 in `#print axioms` 维度。

**Atomic commit**: `.github/workflows/ci.yml` + 可选 audit binary。
**Build verify**: 在本地通过 `act` 或类似工具模拟 CI 执行；Push 后 GitHub Actions verify。
**关闭的 Mathlib standard**: 维度 9（CI / 验证）。
**关闭的 gap**: 无 CI；无 sorry counter；无 axiom audit binary（或文档级近似）。

**⚠️ 战略决策点**: 用户需要 review 是用 shell-grep 简单方案还是 `lake exe` Lean binary 方案。简单方案省事，Lean binary 更精确。建议先 shell-grep（Phase 5.8a），未来升级 binary（Phase 5.8b 或 Phase 6）。

---

## Track C — Convention 调整

### Phase 5.10 — Public API stability 注解

**任务**:
- 在每个 Riemannian 文件的 module docstring 中添加 "Public API" 段（参照 comb_arg README 的 stability section）。
- 列出 stable identifiers vs internal helpers（结构已在 Track A 稳定，names 已确定）。
- 对于 PRE-PAPER stub（如 `ricci_symm` 的 sorry 状态），标注 stability tier 为 "experimental" 或 "PRE-PAPER"。
- 对未来可能 deprecate 的 API（如 `metricInnerRaw`），加 `-- TODO: consider @[deprecated] in v0.2` 注释。

**Atomic commit**: 6 文件 docstring 更新（Riemannian 顶级 facade + 5 模块文件），单 commit。
**Build verify**: `lake build`。
**前置依赖**: Phase 5.4（顶级 facade 必须先存在）。
**关闭的 Mathlib standard**: 维度 6（API surface）。
**关闭的 gap**: API stability 注解缺失。

---

### Phase 5.11 — `@[simp]` / `@[ext]` / `@[simps]` 政策审议

**任务**:
- 全 Riemannian 模块统一审议 `@[simp]` / `@[ext]` / `@[simps]` 标注政策。具体 review:
  - 当前 `@[simp]` 标注（`secondFundamentalFormSqNorm_nonneg`, `manifoldGradientNormSq_nonneg`, `metricToDual_apply`）逐条 review 是否符合 Mathlib simp normal form 标准（confluent、target canonical、无递归）。
  - 当前**未**标 `@[simp]` 但应该标的引理（如 `metricInner_zero_left/right`、`metricInner_neg_left/right` 这类 Mathlib pattern）补标注。
  - `@[ext]` policy on `RiemannianMetric` typeclass — 是否需要 ext lemma? Audit + 决策。
  - `@[simps]` on `RiemannianMetric` typeclass field accessor — 是否需要? Audit + 决策。
- 决策记录在 `docs/CONVENTION_NOTES.md`。

**Atomic commit**: 多文件 attribute 修改 + `docs/CONVENTION_NOTES.md`，单 commit。
**Build verify**: `lake build` + simp 用法测试。
**前置依赖**: Track A 完成（结构稳定，public/internal 已 fixed）。
**关闭的 Mathlib standard**: 维度 3（定理标注）。
**关闭的 gap**: `@[simp]` over-application + 缺漏 + `@[ext]` / `@[simps]` 政策。

---

### Phase 5.12 — Naming polish (subject_verb_object 验收)

**任务**:
- 验收所有 public 名字是否符合 Mathlib subject_verb_object pattern。
- Audit 重点：
  - `metricInnerRaw` — 命名含 "Raw" 后缀，可能不符合 Mathlib pattern。考虑 rename 或 deprecation。
  - `koszulFunctional`、`koszulCovDeriv` — concept-level naming，OK。
  - `manifoldGradient`、`manifoldGradientNormSq` — `manifold` 前缀是否 redundant（`gradient` 单独可能 sufficient，`manifold` 前缀防止与 Mathlib 既有 `gradient` 冲突）。Audit + 决策。
  - 全 lemma 名 audit 是否符合 subject_verb pattern。
- 与 Phase 5.10 的 public API 列表协同 — naming 决定 final 之后才定 API list 的最终 freeze。

**Atomic commit**: 涉及 rename 的多文件修改 + `docs/CONVENTION_NOTES.md` 更新，单 commit。
**Build verify**: `lake build` 全项目 + 下游（GMT 中如有引用 Riemannian names）的 import / call site 检查。
**前置依赖**: Phase 5.10（API list 协同）。
**关闭的 Mathlib standard**: 维度 3（命名约定）+ 维度 6（API surface 终态）。
**关闭的 gap**: naming convention 验收 + `metricInnerRaw` / `manifoldGradient` 命名问题。

---

## 4. 执行顺序总结 — 三轨制 (Critical hot-fix → 结构 → Convention)

按用户战略指引（结构优先，convention 后做）+ critical hot-fix 例外，重排为三轨：

### Track 0 — Critical hot-fix (soundness violation，立即修)

```
Phase 5.0   ricci_symm @[simp] critical fix         [Critical]
```

soundness 问题不能等。`@[simp]` on sorry'd theorem 违反 Mathlib soundness 原则，先移除 `@[simp]` 标注（保留 sorry + repair plan docstring），无需等结构定型。

### Track A — 结构性优化 (先做，破坏性变化集中处理)

```
Phase 5.1   Module docstring headers                 [Major]
Phase 5.2   private + covDeriv 文档化                [Major]
Phase 5.3   冗余 import + variable 块 + open 散布    [Minor]
Phase 5.4   Riemannian 顶级 facade                  [Major]
Phase 5.5   EuclideanSpace concrete instance        [Major]   ⚠️ 战略决策点 1
Phase 5.6   UXTest 补全                              [Minor]
Phase 5.7   Riemannian standalone-able audit         [Major]
```

结构性工作集中在 Track A，理由：
- Facade（5.4）引入后才能确定 stable public API，是后续 convention 工作的对象。
- Concrete instance（5.5）是 typeclass 设计是否合理的实战检验，可能反向 trigger 结构调整。
- UXTest（5.6）补完后，一并 audit standalone-able（5.7）确认 Riemannian 可独立 spin out。
- Track A 结束时，Riemannian 的**结构**（文件组织、namespace、public API 边界、concrete instance、依赖图）已稳定。

### Track B — 验证基础设施 (Track A 之后，convention 之前)

```
Phase 5.8   Axiom registry + sorry catalog           [Major]
Phase 5.9   CI workflow                              [Major]   ⚠️ 战略决策点 2
```

验证基础设施在结构稳定后建立，避免 axiom registry / sorry catalog 在结构变化时反复重写。CI 上线后，Track C 的 convention 调整有了 enforce mechanism。

### Track C — Convention 调整 (后做，针对稳定结构)

```
Phase 5.10  Public API stability 注解               [Major]
Phase 5.11  @[simp] / @[ext] / @[simps] 政策审议    [Minor]
Phase 5.12  Naming polish (subject_verb_object 验收)  [Minor]
```

Track C 的 convention 调整只在**结构稳定**之后做，避免重复工作。
- 5.10 的 public API stability 注解，需要 5.4 的 facade 已存在。
- 5.11 的 `@[simp]` 政策（取代旧的 `secondFundamentalFormSqNorm_nonneg` 单点审议），扩展到全 Riemannian 的 `@[simp]` / `@[ext]` / `@[simps]` 政策统一审议。
- 5.12 的 naming polish 是新增项，验收所有 public 名字是否符合 subject_verb_object pattern；若有不符合，与 5.10 的 public API list 协同调整。

### 总览

```
Track 0: Phase 5.0          [Critical hot-fix]
Track A: Phase 5.1 → 5.7    [结构]
Track B: Phase 5.8 → 5.9    [验证基础设施]
Track C: Phase 5.10 → 5.12  [Convention]
```

13 个 atomic sub-phase。每个 sub-phase 独立 commit + build verify。Track 之间是 hard dependency（A 完成才进 B，B 完成才进 C），Track 内部是 soft dependency（可微调）。

---

## 5. Pre-execution checklist (用户战略决策点)

下面是真正需要用户战略决策的项（**不**要求用户做 implementation choice）：

### ⚠️ 决策点 0: CLAUDE.md edit (Phase 5 的前置)

`docs/PHASE_5_AUDIT.md` 已 propose 5 条 CLAUDE.md edit。建议在 Phase 5 任何 sub-phase 启动前，先 apply 这 5 条 edit 作为 atomic commit，确保 Claude Code 后续执行有正确的 alignment baseline。

### ⚠️ 决策点 1: Phase 5.5 的 concrete instance 选择

Phase 5.5 提供 `EuclideanSpace ℝ (Fin n)` vs `ℝ` 作为 minimal RiemannianMetric instance：
- `EuclideanSpace ℝ (Fin n)`：covers higher-dim case，更接近 Mathlib 风格。
- `ℝ`：1-d 简单 case，更易于 onboarding。
- 也可以两者都做。

**建议**: `EuclideanSpace ℝ (Fin n)` 作为主 example，`ℝ` 作为 minimal 子 example（如有时间）。

### ⚠️ 决策点 2: Phase 5.9 的 CI 实现方案

CI 验证基础设施可以选：
- **方案 A** (轻量): shell-grep based `.github/workflows/ci.yml`。简单，立即可用。
- **方案 B** (Mathlib 风格): `lake exe opengalib-audit` Lean binary，使用 `#print axioms` 进行精确 audit。
- 方案 A → B 是 incremental，可以分两个 sub-phase。

**建议**: Phase 5.9a 实现方案 A；Phase 6 升级到方案 B（如果有 Mathlib upstream PR 计划）。

### ⚠️ 决策点 3: Phase 5 完成后的下一步

Phase 5 完成后（Riemannian 软件工程到 Mathlib 标准），下一步可以是：
- **A**：Phase 5 GMT/MinMax/Regularity 重复（等待 Phase 2/3/4 内容稳定）。
- **B**：Phase 2 cited theorem strict alignment（paper companion 工作）。
- **C**：直接 v0.1 release（如果 Riemannian 的 software engineering 已达 Mathlib 标准且决定先发布 Riemannian standalone lib）。

**建议**: 在 Phase 5 完成时再决定。当前可记录为 Phase 5 完成的 follow-up trigger。

---

## 6. 不在 Phase 5 范围内的项

以下项不属于 Phase 5（明确排除）：
- 数学内容（Phase 4.7.8.C `koszulLeviCivita_exists` 关闭、Phase 4.8 `tangentBundle_symmL_smoothAt` 关闭、`ricci_symm` 实际证明）。
- GMT / MinMax / Regularity 的对应 Phase 5 工作（待对应数学内容稳定后跟进）。
- README / CITATION / LICENSE / CHANGELOG（属于 Phase 6 的 release packaging）。
- Mathlib upstream PR（Phase 6+ 可选）。

---

## 7. 总结

Phase 5 把 Riemannian 模块从「数学内容完整、软件工程部分完整」提升到 Mathlib 软件工程标准。13 个 atomic sub-phase 分为四轨：

```
Track 0: Phase 5.0          [Critical hot-fix — soundness violation]
Track A: Phase 5.1 → 5.7    [结构性优化 — facade / instance / docstring / dependency]
Track B: Phase 5.8 → 5.9    [验证基础设施 — axiom registry / CI]
Track C: Phase 5.10 → 5.12  [Convention 调整 — API stability / @[simp] / naming]
```

**核心原则**: 结构优先，convention 后做。Track A 完成时 Riemannian 的结构（文件、namespace、public API 边界、concrete instance、依赖图）稳定；Track B 上线 enforce mechanism；Track C 在稳定结构上做 convention 标注与 polish，避免重复工作。

3 个用户战略决策点列在 §5（CLAUDE.md edit / Phase 5.5 instance 选择 / Phase 5.9 CI 方案）。

执行模式：用户 review 本 plan + apply CLAUDE.md edit → 用户对决策点 1-3 做战略 call → Claude (chat) 把每个 sub-phase 翻译成 Claude Code prompt → Claude Code 顺序执行 + build verify + atomic commit。

完成后 Riemannian 模块达到「复用性极高、极其优秀的软件工程、至少达到 Mathlib 标准」的用户战略目标。
