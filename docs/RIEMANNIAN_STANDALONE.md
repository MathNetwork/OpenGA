# Riemannian — Standalone Spin-out Audit

**日期**: 2026-04-28
**目的**: 验证 `Riemannian/` 模块可以从 OpenGALib 独立 spin out 为 standalone Lean lib（Mathlib upstream / Lean 社区使用）。

---

## 依赖审计

### 外部依赖（仅 Mathlib）

`Riemannian/` 全部 17 个 import 行（含 facade）的外部依赖：

```
Mathlib.Analysis.InnerProductSpace.Basic
Mathlib.Analysis.InnerProductSpace.LinearMap
Mathlib.Analysis.InnerProductSpace.PiL2
Mathlib.Analysis.SpecialFunctions.SmoothTransition
Mathlib.Geometry.Manifold.BumpFunction
Mathlib.Geometry.Manifold.ContMDiff.Basic
Mathlib.Geometry.Manifold.IsManifold.Basic
Mathlib.Geometry.Manifold.MFDeriv.Basic
Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
Mathlib.Geometry.Manifold.VectorBundle.Tangent
Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
Mathlib.Geometry.Manifold.VectorField.LieBracket
Mathlib.LinearAlgebra.Trace
```

**结论**: 仅依赖 Mathlib。**零 cross-package 依赖**（GMT / MinMax / Regularity / AltRegularity 均未被 Riemannian 引用）。

### 内部依赖（Riemannian.* 自身）

```
Riemannian.BumpFunction
Riemannian.Connection
Riemannian.Curvature
Riemannian.Gradient
Riemannian.Instances.EuclideanSpace
Riemannian.Metric
Riemannian.SecondFundamentalForm
```

DAG（无循环）:
```
Metric ← Connection ← {Curvature, Gradient, SecondFundamentalForm}
       ←──────────── Instances.EuclideanSpace
BumpFunction (independent — only depends on Mathlib)
```

---

## Namespace 审计

`Riemannian/` 使用的 namespaces:

- `Riemannian` — 主要数学概念命名空间（covDeriv, riemannCurvature, ricci, scalarCurvature, secondFundamentalFormScalar, manifoldGradient, ...）
- `OpenGALib` — 框架级 typeclass + 相关操作（RiemannianMetric, metricInner, metricRiesz, metricToDual, instRiemannianMetricSelf, ...）
- `OpenGALib.BumpFunction` — bump 函数子命名空间
- `OpenGALib.RiemannianMetric` — typeclass 内部访问器（metricInnerRaw）

**Paper-domain leakage 检查**: 无。namespaces 全部 concept-level，无 person-level（无 Wickramasekera, AlmgrenPitts），无 paper-specific 概念。

---

## Spin-out 步骤

要把 `Riemannian/` 独立为 standalone Lean lib `OpenGALibRiemannian`：

1. **建仓**: 新建 `OpenGALibRiemannian/` git repo。
2. **复制内容**:
   - `Riemannian.lean` → repo 顶级 `OpenGALibRiemannian.lean`（顶级 facade）
   - `Riemannian/*.lean` → `OpenGALibRiemannian/`（保留目录结构）
   - `Riemannian/Instances/EuclideanSpace.lean` → `OpenGALibRiemannian/Instances/EuclideanSpace.lean`
3. **改 import 前缀**:
   - `Riemannian.X` → `OpenGALibRiemannian.X`（约 7 个 import 语句）
   - 或保留 `Riemannian` 作为 namespace 但改 module 名为 `OpenGALibRiemannian`
4. **`lakefile.lean`**: copy 当前 `lakefile.lean` 中 `Riemannian` 子段，独立成新 lakefile。
5. **`lake-manifest.json`**: pin Mathlib SHA。
6. **`lean-toolchain`**: 拷贝当前版本。
7. **License / README / CITATION**: 添加 (Phase 6 内容)。

---

## 与 OpenGALib 的对接（spin-out 后）

OpenGALib 仍可消费 spin-out 后的 `OpenGALibRiemannian` 通过：

```lean
-- OpenGALib lakefile.lean
require OpenGALibRiemannian from git "https://github.com/.../OpenGALibRiemannian"
```

当前 OpenGALib 内部消费 `Riemannian.*` 的位置：
- `GeometricMeasureTheory/Variation/FirstVariation.lean` — uses `Riemannian.covDeriv`, `Riemannian.metricInner`
- `GeometricMeasureTheory/HasNormal.lean`、`Variation/SecondVariation.lean` 等 — 类似

Spin-out 后这些 import 行从 `import Riemannian.*` 改为 `import OpenGALibRiemannian.*`，行为完全不变。

---

## 阻塞 spin-out 的项

**无**。Phase 5 完成后，Riemannian 模块 standalone-able 验收通过。

PRE-PAPER sorry'd statements（`ricci_symm`, `ricciTraceMap.map_*`）和结构性 axioms（`tangentBundle_symmL_smoothAt`, `koszulLeviCivita_exists`）不阻塞 spin-out — 它们是 lib content 本身的状态，不是模块化 boundary 问题。

---

## 总结

`Riemannian/` 模块 spin-out 评估：**通过**。

- 仅依赖 Mathlib
- 无 cross-package 依赖
- 无 paper-domain leakage
- 命名空间清晰（concept-level）
- DAG 无循环
- 顶级 facade + Public API 列表完整（`Riemannian.lean`）
- 配套 concrete instance（`Instances/EuclideanSpace.lean`）

实际 spin-out 时机：Phase 6（pre-release packaging）。
