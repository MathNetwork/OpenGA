# 2026-06-12 · SmoothManifoldsLee 大分支整合方案

**事件**：LehengChen 推送 `import/smooth-manifolds-lee`（`a5f308c`）：Lee《Introduction to Smooth Manifolds》Ch1–5 的形式化，346 文件 / 6.2 万行，仅依赖 Mathlib，与 OpenGALib 零依赖零重复。当日全量审计：**187 全新 / 95 Mathlib 重复 / 57 部分重复；52 个高价值文件**。明细与施工台账见同目录 `WORKLIST.md`。

## 问题

这批材料是**教材序的形式化**：一个编号一个文件、import 图与章节耦合、设施代码（图卡操作、截断函数、实例打包）散落在各章定理脚下随用随造。我们要的是**高复用、可维护、可延伸的软件**：声明按数学对象组织、设施沉淀为共用层、上层只 import 设施而不知道教材的存在。

所以要回答的是：**教材序形式化 → 软件库的转化怎么做，并且做成可重复的流程**——这不会是最后一次有人带着一整本书的形式化来敲门。

## 分支与流程

```
import/<source>    冻结参考快照（只读，永不 merge，staging/ 不进主干）
      ↓ 人工/AI 移植，非 git merge
port/<工单>        短命施工分支，一单一支，从 develop 切出
      ↓ PR + CI + review
develop → main     现有惯例不变
```

- import 分支永不合并：外来约定不进历史，且审计结论只对锚定的快照 commit 有效。上游再有新货推 `import/<source>-v2`，diff 出增量、只重审增量，不 force-push。
- 每个 port PR 的质量门：命名空间已换、落点符合布局、**零 sorry**、提交前**全量 `lake build`**、模块 docstring 带出处行（`Ported from <source> <path> (<commit>)`）、linter 基线无新增违例。
- 领单即在 `WORKLIST.md` 台账改状态，台账改动随移植 PR 同行；不碰别人 in-progress 的单。
- 全部移植完：参考分支打 tag 归档后删除，台账存档作为出处记录。

## 自动化流水线（设想，待试点）

9 张施工单是同构单元，每单走同一循环，自动化程度由试点数据决定：

```
领单 → ① 通用层判定（AI 输出 复用/扩展/新建 决策表，必须附 grep 证据）
     → ② 移植（AI：换命名空间、重组、每条声明补 Math./Eng. 双 docstring）
     → ③ 机器门（CI：全量构建、零 sorry、linter、命名与出处检查）
     → ④ 自动开 PR（附决策表与台账 diff）
     → ⑤ 人审（只审两项，见下节）
```

两条**常驻约束**写进 AI 任务模板，不靠口头提醒：

1. **通用层优先**：未回答"主分支是否已有同型设施"之前不许写代码。本次审计已验证必要性——两边各写了同一组设施的一半（图卡演算、截断函数、打包类）。
2. **语义符合**：每条声明带 Math./Eng. 双 docstring（范例 `Riemannian/TangentBundle/TangentSmooth.lean`）。存在性 linter 把守，忠实性人审把守。

自动化终点是 PR，不是 develop。人始终是合并守门员。

## 人的部分：评审怎么分配

依据最小可信基（minimal trusted base）：Lean 内核已检查全部证明，**证明不用人审**；但定义错了，内核会让我们证明几千行关于错误对象的真命题。人审对象收缩为**定义与陈述**，其中定义错误废整个下游依赖锥，定理陈述错误只废自己。

1. **核心节点清单**：依赖图入度高的 `def`/`class`/`structure` 入选（实测承重墙：`IsEmbeddedSubmanifold` 被引 18 次、`TopologicalManifold` 17 次），人工增补语义微妙者；`theorem` 一般不入选。
2. **CODEOWNERS**：核心节点文件映射到数学专家，无 owner 批准不能合并（GitHub 机制强制）。
3. **专家只审两件事**：Math. docstring 与陈述是否同一数学对象；核心定义的实例化测试是否非空洞（example 进 `Tests/`，如"球面是 `IsEmbeddedSubmanifold`"，堵"假设不可满足、空洞为真"）。
4. 非核心节点：AI 审 + 抽查。

一句话：内核消灭了证明审查，剩余负担集中在可信基，可信基里承重的是依赖图枢纽——枢纽钉给专家，用最少的专家时间买全局正确性。

## 待团队决定

- [ ] 三个新 linter（docstring 对、命名空间白名单、出处行）进 `OpenGALib/Util/Linter/`？
- [ ] 核心节点入度阈值（建议 ≥ 5，首版清单随工单 #1 提交）
- [ ] CODEOWNERS 映射：流形地基 / 子流形与切片 / 带边与几何测度论接口各归谁
- [ ] 自动开 PR 触发方式：本地脚本 / GitHub Action / 定时 agent
- [ ] 人审时限（建议核心节点 PR 三个工作日内响应）

**试点**：工单 #1（`port/manifold-typeclass-core`）半手工走完整循环，校准模板与 linter；按返工率和人审发现数决定 #2–9 的自动化深度。

---
关联：PR #60 · `import/smooth-manifolds-lee`（`a5f308c`）
