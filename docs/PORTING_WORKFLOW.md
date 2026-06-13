# 外部形式化成果的移植工作流（常设）

把"以教材/论文为序的外部形式化"转化为本库模块的**可重复流程**。本文档是常设的库级规范，不绑定具体来源；首个实例是 SmoothManifoldsLee（方案与逐章台账见 `log/2026-06-12-smooth-manifolds-lee/` 的 PLAN.md / WORKLIST.md，总追踪 issue #61）。

## 1. 分支模型

```
import/<source>      冻结参考快照（只读）
      ↓ 人工/AI 移植（拆分重组，非 git merge）
port/<工单slug>      短命施工分支，一单一支
      ↓ PR + 质量门 + 人审
develop → main       现有惯例不变
```

**import 分支规则**：

- 永不 merge、永不 force-push、`staging/` 不进主干。审计与出处结论只对锚定的快照 commit 有效。
- 上游有后续产出，推 `import/<source>-v2`（v3 依此类推）增量快照，只重审增量。
- 全部移植完成后：打 tag 归档，删除分支；台账存档为出处记录。

**port 分支规则**：

- 一张施工单一条分支一个 PR；分支名 `port/<工单slug>`，与台账工单一一对应。
- 移植不是搬运：换命名空间、按 `NAMING_CONVENTION.md` 重排落点、每条声明补 Math./Eng. 双 docstring、模块头加出处行 `Ported from <source> <path> (<commit>)`。
- 合并目标始终是 `develop`。

## 2. PR 拆分与排序（develop merge 有延迟时的并行规则）

1. **无依赖的工单并行**：各自从 `develop` 切出，PR base 指 `develop`，互不等待。
2. **有依赖的工单不等上游 merge**：从上游 port 分支切出，PR base 设为上游 port 分支（GitHub stacked PR）。上游 merge 并删除分支后，GitHub 自动将下游 PR 的 base retarget 到 `develop`；下游 rebase 一次后进入 review。base 机制由 GitHub 强制"下游不可能先合"，不靠自觉。
3. **rebase 责任在下游**：上游 merge 后，下游工单负责及时 rebase（自动化后由 bot 执行）。
4. **防冲突约定**：每单只允许改三类文件——(a) 本单的新目标模块文件；(b) 本单的台账工单 YAML；(c) 域索引文件的 import 行。(c) 是唯一共享触点：单独成 commit、按字母序插入，把冲突面压到行级。
5. **拆单原则**：一单内容应是同一设施层/同一数学对象簇；跨层内容拆成有依赖关系的多单走 stacked，不做巨型 PR。

## 3. 迁移台账（状态可记录、可审计）

台账分两层：

- **状态层（事实源）**：`docs/ledger/tickets/NN-<slug>.yaml`，一单一文件，住本仓库、随 port PR 同行受审。字段：id / slug / title / branch / deps / state / assignee / pr / rework_count / source（锚定 import commit）/ gates（最近一次质量门结果）。
- **事件层（运行记录）**：append-only 事件日志由 bot 工作区持有，不进本仓库历史。

工单状态机（非法迁移会被工具拒绝；打回走 rework，返工计数 +1）：

```
todo → claimed → porting → gated → pr-open → in-review → merged → archived
                    ↑__________________________________|（gate 失败 / 人审打回）
```

状态迁移只通过台账工具（portbot CLI）执行，不手改 `state` 字段；台账 YAML 的变更与对应代码变更同 PR 提交。`rework_count` 是校准自动化深度的核心数据。

## 4. 质量门（确定性，机器执行，本地与 CI 同一份脚本）

| gate | 检查 |
|---|---|
| build | 全量 `lake build` 通过 |
| no-sorry | 相对 develop 改动的 `.lean` 文件零 sorry |
| namespace | 顶层 namespace 在白名单内（教材式通用命名空间不得进库） |
| provenance | 改动文件含出处行 `Ported from <source> <path> (<commit>)` |
| docstring | 声明带 Math./Eng. 双 docstring（存在性机器把守，忠实性人审把守） |
| linter-baseline | linter 违例数不高于基线 |

全部 gate 通过是开 PR 的前置条件（工单 `porting → gated`）。

## 5. 人审（最小可信基）

Lean 内核已检查全部证明，证明不用人审；人审收缩为**定义与陈述**：

- 依赖图入度高的核心 `def`/`class`/`structure` 列入核心节点清单，经 CODEOWNERS 映射到数学专家，无 owner 批准不能合并。
- 专家只审两件事：Math. docstring 与陈述是否同一数学对象；核心定义的实例化测试是否非空洞。
- 非核心节点：AI 审 + 抽查。

## 6. 不变式

- 自动化终点是 PR，**人是合并守门员**，bot 不 merge。
- `import/*` 永不 merge；sorry 不进主干；状态迁移必经台账留痕。

---

工具实现（portbot：台账 CLI + gate 脚本 + runner）目前在独立工作区仓库开发，成熟后另行开源；本文档只规定流程本身，流程不依赖特定工具。
