# SmoothManifoldsLee 整合工单

来源：分支 `import/smooth-manifolds-lee`（commit `a5f308c`，LehengChen，2026-06-12），内容为 Lee《Introduction to Smooth Manifolds》第 1–5 章的 Lean 4 形式化，自包含、仅依赖 Mathlib（v4.30.0），与 OpenGALib 现状零依赖关系。

本工单由 2026-06-12 的全量重叠审计产出：40+ 个并行 agent 逐文件对照 Mathlib（`.lake/packages/mathlib`）与 OpenGALib 判重、定级、给出落点建议。审计覆盖全部 346 个章节文件（339 个批量审计 + 7 个深层子目录文件补审）。

## 总体统计

| 维度 | 分布 |
|---|---|
| 重叠分类 | new 187 · mathlib-dup 95 · partial-dup 57 |
| 移植价值 | high 52 · medium 101 · low 186 |
| 含 sorry 文件 | 106 |

约 28% 的文件实质重复 Mathlib（多为带教材编号的包装/复述），直接跳过；187 个全新文件是移植主体。

## 整合原则

1. **按目标模块移植，不按章节顺序**。教材组织（`ChapNN/SecNN_MM/`）不进主库；声明按数学对象重组进领域模块。
2. **声明名基本可保留**（已是 Mathlib 风格描述性命名），但命名空间必须换掉（staged 代码用了 `Manifold` 等通用命名空间），文件结构按 `../../NAMING_CONVENTION.md` 重排。
3. **打包类收编进现有体系**：`TopologicalManifold n M` 等类只是 Mathlib 实例（T2 + 第二可数 + `ChartedSpace`）的打包，与我们已有的 `SmoothManifold M` 打包类（`Riemannian/Manifold/SmoothManifold.lean`）是同一设计模式。移植时统一收编进我们的打包类体系，不引入第二套；维数显式化（`n` 参数）是否保留在收编时定夺。
   - 与 OpenGALib 的重叠：全量审计为 0 个 `opengalib-dup`——我们库直接踩在 Mathlib 流形机器上做度量层以上的内容，Lee 覆盖的子流形/浸入/坐标球层我们完全没有。唯一接口接触点：`GeometricMeasureTheory/Varifold.lean` 的 `LocalSmoothEmbeddingWitness` 临时证人结构，嵌入子流形理论移植后应垫到其下并替换之。
4. **sorry 不进主干**：含 sorry 的文件要么先补证明，要么陈述层有 sorry 的（如 Chap04 的 `rankAt`/`HasConstantRank`）整段推迟。
5. **落点归一化**：下文 agent 建议的 targetModule 路径风格不一（`Riemannian/Manifold/…`、`Riemannian/Submanifold/…` 等），施工时统一收敛到一个顶层流形域（待定名，候选 `OpenGALib/SmoothManifold/`），垫在 `Riemannian` 与 `GeometricMeasureTheory` 之下。
6. 工具链先升级：staged 代码用 Lean v4.30.0 正式版，我们在 rc2，第一批移植前对齐。

## 共用抽象设施层

两边各自实现了同一组设施的两半（我们：度量/测度面向；他们：拓扑/嵌入面向）。合并时以下五层作为共用模块进主分支，两边上层各自 import：

| 设施层 | OpenGALib 已有 | staged 分支提供 | 备注 |
|---|---|---|---|
| 流形打包类 | `SmoothManifold M`、`RiemannianManifold M` | `TopologicalManifold n M`、`SmoothManifoldWithBoundary n M` | 收编为一条谱系；**带边支持是我们的空白，且是 GMT 散度定理的前提** |
| 图卡演算 | `Riemannian/Volume/Util/ChartOverlap.lean`、`ChartTransition.lean` | 坐标球、居中图卡、预紧坐标球、欧氏切片坐标 | 同源设施各写一半，应独立成共用 `Charts` 模块，从 `Volume/Util/` 迁出 |
| 截断/单位分解 | `Riemannian/Manifold/BumpFunction.lean` | 环形截断、单位分解存在性、穷竭函数 | 都在包装同批 Mathlib 原语，合并为一个平滑化模块 |
| 切丛局部化 | `Riemannian/TangentBundle/TangentSmooth.lean`（`trivAt` 判据） | 切丛平凡化、点导子、曲线速度 | 跟施工顺序第 4 站走 |
| 子流形抽象 | `Varifold.lean` 的 `LocalSmoothEmbeddingWitness`（临时证人） | `IsEmbeddedSubmanifold` + 切片图卡理论 | 跟施工顺序第 2 站走，移植后替换证人结构 |

设施层 1–3 小、基本无 sorry、两边消费者均已存在，适合作为第一批合并内容，priority 高于按章节移植。

## 施工台账

流程见 `PLAN.md`（领单改状态、一单一 `port/` 分支、质量门、销单）。施工单按依赖序排列；标注"可并行"的单之间无依赖。

| # | 施工单 | 内容 | 依赖 | 状态 |
|---|---|---|---|---|
| 1 | `port/manifold-typeclass-core` | 设施层 1：打包类谱系合并（`TopologicalManifold n M`、带边流形类收编进 `SmoothManifold M` 谱系；Chap01 Sec01/Sec01_06） | — | todo |
| 2 | `port/charts` | 设施层 2：图卡演算共用模块（坐标球、居中图卡 + 现有 `ChartOverlap`/`ChartTransition` 迁出合并） | #1 | todo |
| 3 | `port/cutoffs` | 设施层 3：截断/单位分解/穷竭函数并入 `BumpFunction` 体系（Chap02 Sec02_10/11 高价值条目） | #1 | todo（与 #2 可并行） |
| 4 | `port/embedded-submanifold` | 设施层 5 上半：`IsEmbeddedSubmanifold` + 图论式子流形 API（Chap05 Sec05_28） | #2 | todo |
| 5 | `port/slice-charts` | 设施层 5 下半：切片定理基础设施（`Theorem_5_8/` 全家 + Sec05_29） | #4 | todo |
| 6 | `port/submersion-covering` | 浸没/浸入/覆盖映射（Chap04 Sec04_25/26 高价值簇） | #2 | todo（与 #4–5 可并行） |
| 7 | `port/tangent-localization` | 设施层 4：切丛局部化（平凡化、点导子、曲线速度；Chap03 高价值条目） | #1 | todo（与 #2–6 可并行） |
| 8 | `port/varifold-witness-swap` | `LocalSmoothEmbeddingWitness` 替换为子流形理论 | #5 | todo |
| 9 | （按需）medium 条目 | 见各章节"可考虑"表 | 视条目 | backlog |

前置事项（不占施工单）：工具链对齐 v4.30.0 正式版。

## 补审：深层子目录文件（批量审计遗漏，已补）

| 文件 | 主要声明 | 分类 | 价值 | sorry | 理由 |
|------|----------|------|------|-------|------|
| Chap05/Sec05_29/Theorem_5_8/Common.lean | euclidean_slice_projection 等 27 条 | new | high | 否 | 欧氏切片几何与图卡居中基础设施 |
| Chap05/Sec05_29/Theorem_5_8/Index.lean | 重导出 | new | medium | 否 | 索引文件 |
| Chap05/Sec05_29/Theorem_5_8/LocalNormalFormAPI.lean | rank_normal_form 等 | partial-dup | medium | 否 | 包装 Mathlib 浸入正规形式，桥接第 4 章秩形式 |
| Chap05/Sec05_29/Theorem_5_8/LocalSliceAtlas.lean | slice_condition_chartAt 等 30+ 条 | new | high | 否 | 切片条件图册构造核心 |
| Chap05/Sec05_29/Theorem_5_8/LocalSliceImmersion.lean | local_slice_condition_has_embedded_submanifold_structure 等 11 条 | new | high | 否 | 切片上嵌入子流形结构的完成步 |
| Chap05/Sec05_36/Theorem_5_51/EuclideanHalfSlice.lean | euclidean_half_slice_projection_partial_homeomorph | new | medium | 是 | 半切片边界图卡的半成品 |
| Chap05/Sec05_36/Theorem_5_51/Index.lean | 重导出 | new | low | 是 | 下游未实现 |

---

# Chap01

## 移植优先（high，10 项）

| 文件 | 声明 | 分类 | 落点 | sorry | 理由 |
|---|---|---|---|---|---|
| Sec01/Definition_1_extra_2.lean | IsCoordinateBall, centerAt 等 | new | Manifold/Charts | 否 | 坐标球/盒卡形谓词，Mathlib 缺，坐标球栈基础 |
| Sec01/Example_1_5.lean | RealProjectiveSpace, realProjectiveChart 等 | new | Instances/ProjectiveSpace | 否 | RP^n 商拓扑与标准仿射卡，Mathlib 完全缺失 |
| Sec01/Example_1_8.lean | contDiffGroupoid_pi, instIsManifoldPi 等 | new | Instances/Pi | 否 | 有限乘积 IsManifold 实例，补 Mathlib 已注明缺口 |
| Sec01/Lemma_1_10.lean | isTopologicalBasis_isPrecompactCoordinateBall 等 | new | Manifold/Charts | 否 | 预紧坐标球可数基，单位分解/穷竭列底层 |
| Sec01_03/Definition_1_3_extra_1.lean | IsSmoothCoordinateBall, IsRegularCoordinateBall 等 | new | Manifold/CoordinateBall | 否 | 光滑/正则坐标球谓词全证，需脱离项目内依赖 |
| Sec01_04/Example_1_32.lean | regular_level_set_smooth_structure 等 | new | Manifold/RegularLevelSet | 否 | 正则水平集定理 1750 行全证，Mathlib 无正则值定理 |
| Sec01_04/Lemma_1_35.lean | ChartedSpaceCore.toTopologicalSpace_t2Space, toChartedSpace_isManifold 等 | new | Manifold/ChartedSpaceCore | 否 | 由图册造流形的 T2/二可数/光滑判据，Mathlib 缺 |
| Sec01_06/Exercise_1_42.lean | IsRegularCoordinateHalfBall 等 | new | Manifold/CoordinateBalls | 是 | 正则坐标(半)球可数基，三定理全 sorry |
| Sec01_07/Problem_1_9.lean | ComplexProjectiveSpace, complexProjectiveSpaceIsManifold 等 | new | Instances/ComplexProjectiveSpace | 否 | CP^n 完整流形结构无 sorry，Fubini-Study 宿主 |
| Sec01_05/Proposition_1_40.lean | IsBoundaryModelCoordinateBall, countable_fundamentalGroup 等 | partial-dup | Manifold/CoordinateBall | 是 | 半球基与可数基本群为缺口，拓扑推论 Mathlib 已有，全 sorry |

<details><summary>可考虑（medium，21 项）</summary>

| 文件 | 声明 | 分类 | 落点 | sorry | 理由 |
|---|---|---|---|---|---|
| Sec01/Exercise_1_1.lean | HasCoordinateBallCharts 等 | new | Manifold/Charts | 否 | 卡收缩/拉直引理完整，存在式陈述需重构 |
| Sec01/Exercise_1_6.lean | realProjectiveSpace_t2Space 等 | new | Instances/ProjectiveSpace | 是 | 补 Example_1_5 所需 T2/二可数，四条全 sorry |
| Sec01/Exercise_1_7.lean | realProjectiveSpaceCompactSpace | new | Instances/ProjectiveSpace | 否 | RP^n 紧性全证，宜随 Example_1_5 一并移植 |
| Sec01_03/Proposition_1_19.lean | exists_countable_regular_coordinate_ball_basis 等 | new | Manifold/CoordinateBall | 是 | 正则坐标球可数基有用，证明 sorry 且打包需重构 |
| Sec01_04/Example_1_30.lean | graph_coordinate_chart, graph_charted_space 等 | new | Manifold/GraphChart | 是 | 光滑映射图卡空间为缺口，关键引理 sorry |
| Sec01_04/Example_1_33.lean | realProjectiveSpaceIsManifold, realProjectiveChartTransitionDiffeomorph 等 | new | Instances/RealProjectiveSpace | 否 | ℝPⁿ 光滑结构全证，需先移上游 Example_1_5 |
| Sec01_06/Definition_1_6_extra_1.lean | contMDiffOn_halfSpace_iff_forall_exists_smoothAmbientExtension 等 | new | Manifold/HalfSpaceExtension | 是 | 半空间环境延拓光滑判据，关键边界引理 sorry |
| Sec01_06/Definition_1_6_extra_3.lean | IsSmoothCoordinateHalfBall 等 | new | Manifold/CoordinateBalls | 是 | 与 Exercise_1_42 定义重叠，需先合并 API |
| Sec01_07/Problem_1_10.lean | problem_1_10_chart_matrix, block_column_subspace 等 | new | GeometricMeasureTheory/Grassmannian/Charts | 是 | Grassmann 矩阵坐标可喂 varifold，主定理全 sorry |
| Sec01_07/Problem_1_11.lean | closed_unit_ball_smoothManifoldWithBoundary 等 | new | SmoothManifold/ClosedBall | 是 | 闭球带边流形补缺口，关键定理 sorry，图册取自 Problem_2_4 |
| Sec01_07/Problem_1_5.lean | sigmaCompactSpace_of_connected_paracompact_locallyCompact_t2 等 | new | Manifold/Paracompactness | 否 | 仿紧⇒σ紧逆向及二可数刻画，Mathlib 仅有正向 |
| Sec01_07/Problem_1_6.lean | supportedRadialTwistHomeomorph, exists_uncountably_many_distinct_smooth_structures 等 | new | Manifold/SmoothStructures | 否 | 不可数多光滑结构全证，多为单定理脚手架 |
| Sec01/Definition_1_extra_1.lean | TopologicalManifold, dimension_eq 等 | partial-dup | Manifold/TopologicalManifold | 是 | C⁰流形打包类，多为包装且维数不变 sorry |
| Sec01/Example_1_3.lean | graphMap, graph_coordinates 等 | partial-dup | Manifold/Charts | 否 | 打包同胚 graphOn≃ₜU 为 Mathlib 缺，GMT 图参数化常用 |
| Sec01/Theorem_1_15.lean | exists_countable_locallyFinite_refinement_of_isTopologicalBasis 等 | partial-dup | Manifold/Charts | 否 | 预紧坐标球可数局部有限加细，喂单位分解 |
| Sec01_02/Definition_1_2_extra_3.lean | IsSmoothAtlas 等 | partial-dup | SmoothManifold/Atlas | 否 | 不依实例的图册谓词为新，属小众脚手架 |
| Sec01_02/Proposition_1_17.lean | same_smooth_structure_iff_union_is_smooth_atlas 等 | partial-dup | SmoothManifold/Atlas | 否 | 并集判同光滑结构为新，letI 陈述需重构 |
| Sec01_04/Example_1_36.lean | grassmannian, grassmannian.chart_equiv 等 | partial-dup | Instances/Grassmannian | 是 | Grassmann 卡双射缺口，非平凡引理全 sorry |
| Sec01_05/Proposition_1_38.lean | boundaryChart, boundaryTopologicalManifold 等 | partial-dup | Manifold/InteriorBoundary | 是 | 边界作(n-1)流形构造，近全 sorry 且绑定专有模型 |
| Sec01_06/Exercise_1_44.lean | ModelWithCorners.interiorOpens 等 | partial-dup | Manifold/InteriorBoundary | 否 | 内部为无边开子流形等小引理，补全边界设施 |
| Sec01_06/Theorem_1_46.lean | isInteriorPoint_iff_of_mem_maximalAtlas 等 | partial-dup | Manifold/InteriorBoundary | 否 | 边界检测推广到极大图册卡，全证 |

</details>

<details><summary>跳过（44 项，绝大多数为 Mathlib 包装/recall 文件）</summary>

- Sec01/Definition_1_extra_3.lean — mathlib-dup — 纯 recall 类型类
- Sec01/Definition_1_extra_4.lean — mathlib-dup — recall 加薄包装
- Sec01/Example_1_4.lean — mathlib-dup — 球面实例一行复包
- Sec01/Example_1_9.lean — new — 平凡 abbrev
- Sec01/Exercise_1_14.lean — mathlib-dup — 纯 recall
- Sec01/Lemma_1_13.lean — mathlib-dup — 与 Exercise_1_14 重复
- Sec01/Proposition_1_11.lean — partial-dup — recall 加实例装配
- Sec01/Proposition_1_12.lean — mathlib-dup — 纯 recall 包装
- Sec01/Proposition_1_16.lean — new — 一行 simpa 引 1.40
- Sec01/Theorem_1_2.lean — new — recall 项目 sorry 定理
- Sec01_02/Definition_1_2_extra_1.lean — mathlib-dup — #check 指针
- Sec01_02/Definition_1_2_extra_2.lean — partial-dup — 两行包装
- Sec01_02/Definition_1_2_extra_4.lean — mathlib-dup — recall 指针
- Sec01_02/Definition_1_2_extra_5.lean — mathlib-dup — rfl 即得且 sorry
- Sec01_02/Exercise_1_18.lean — mathlib-dup — 零声明指针
- Sec01_02/Remark_1_2_extra_6.lean — mathlib-dup — recall 指针
- Sec01_03/Exercise_1_20.lean — new — 复述 1.19 无新声明
- Sec01_03/Notation_1_3_extra_2.lean — mathlib-dup — extChartAt recall
- Sec01_04/Example_1_21.lean — partial-dup — 离散流形薄装配
- Sec01_04/Example_1_22.lean — mathlib-dup — sorry 复述实例
- Sec01_04/Example_1_23.lean — new — 一次性反例无 API
- Sec01_04/Example_1_24.lean — mathlib-dup — 薄组合/#check
- Sec01_04/Example_1_25.lean — mathlib-dup — 一行推论加 #check
- Sec01_04/Example_1_26.lean — mathlib-dup — 纯 #check
- Sec01_04/Example_1_27.lean — mathlib-dup — #check 加 sorry 辅理
- Sec01_04/Example_1_28.lean — partial-dup — 关键开性 sorry
- Sec01_04/Example_1_29.lean — mathlib-dup — 两步推论
- Sec01_04/Example_1_31.lean — mathlib-dup — 球面实例 #check
- Sec01_04/Example_1_34.lean — mathlib-dup — 复述乘积实例
- Sec01_04/Notation_1_4_extra_1.lean — mathlib-dup — 记号对照 #check
- Sec01_05/Definition_1_5_extra_1.lean — partial-dup — 半空间模型笨拙打包
- Sec01_05/Exercise_1_39.lean — mathlib-dup — 零声明 #check
- Sec01_05/Exercise_1_41.lean — partial-dup — 纯指针文件
- Sec01_05/Theorem_1_37.lean — mathlib-dup — 单条 recall
- Sec01_06/Definition_1_6_extra_2.lean — mathlib-dup — 类复包 Mathlib
- Sec01_06/Exercise_1_43.lean — mathlib-dup — 零声明 #check
- Sec01_06/Proposition_1_45.lean — mathlib-dup — 纯 recall
- Sec01_07/Problem_1_1.lean — new — 双原点反例无 API
- Sec01_07/Problem_1_12.lean — mathlib-dup — infer_instance 直调
- Sec01_07/Problem_1_2.lean — partial-dup — 习题级薄组合
- Sec01_07/Problem_1_3.lean — mathlib-dup — 双向薄包装
- Sec01_07/Problem_1_4.lean — new — 近平凡引理加反例
- Sec01_07/Problem_1_7.lean — mathlib-dup — 重造球极图册多 sorry
- Sec01_07/Problem_1_8.lean — partial-dup — 圆专用习题

</details>

## 小结

第一章共审计 75 个文件，约六成是对 Mathlib 既有结果的 recall、#check 或薄封装，可直接跳过。真正值得移植的核心资产集中在两条线：一是坐标球/覆盖基础设施（坐标球谓词、预紧坐标球可数基、正则坐标(半)球），它们是单位分解、穷竭列与 GMT 覆盖论证的底层；二是实例级缺口（RP^n、CP^n 的完整流形结构、有限乘积 IsManifold 实例、正则水平集定理、ChartedSpaceCore 构造引理），均为 Mathlib 公认空白且大多 sorry-free。中等价值条目多数受 sorry 残留或项目内部依赖（TopologicalManifold 类、LeeBoundaryModelSpace）牵制，移植前需先做 API 重构与依赖消解。

---

# Chap02

## 移植优先（high，4 项）

| 文件 | 声明 | 分类 | 落点 | sorry | 理由 |
|---|---|---|---|---|---|
| Sec02_12/Problem_2_4.lean | closed_unit_ball_fixed_atlas, split_at_coordinate 等 | new | Instances/ClosedBall | 否 | 闭球带边流形 2600 行无 sorry，直撑 GMT 散度定理 |
| Sec02_11/Proposition_2_28.lean | exists_positive_smooth_exhaustion_function | new | Manifold/Exhaustion | 否 | 正光滑穷竭函数全证，非紧 L²/Bochner/GMT 所需 |
| Sec02_09/Example_2_14.lean | unitOpenBallDiffeomorph, smoothChartDiffeomorph 等 | partial-dup | Manifold/Diffeomorph | 否 | 打包单位球≃ℝⁿ与卡微分同胚，Mathlib 仅散装引理 |
| Sec02_09/Proposition_2_15.lean | Diffeomorph.pi, Diffeomorph.restrictOpen 等 | partial-dup | Manifold/Diffeomorph | 是 | 乘积与开子流形限制 API 为缺口，六条辅理 sorry |

<details><summary>可考虑（medium，14 项）</summary>

| 文件 | 声明 | 分类 | 落点 | sorry | 理由 |
|---|---|---|---|---|---|
| Sec02_09/Theorem_2_17.lean | Diffeomorph.dimension_eq 等 | new | Manifold/Diffeomorph | 否 | 微分同胚维数不变全证，Mathlib 缺此通用引理 |
| Sec02_11/Definition_2_11_extra_2.lean | Function.IsSmoothOn 等 | new | Manifold/SmoothExtension | 否 | 子类型域局部延拓光滑谓词，需对齐 ContMDiffOn |
| Sec02_11/Definition_2_11_extra_3.lean | Function.IsExhaustionFunction 等 | new | Manifold/Exhaustion | 否 | 穷竭函数类与 proper 引理，2.28 的 API 基础 |
| Sec02_11/Lemma_2_26.lean | exists_supported_contMDiffMap_extension_of_isClosed | new | Manifold/SmoothExtension | 是 | 闭集光滑延拓为真缺口，仅有陈述需从头证 |
| Sec02_12/Problem_2_10.lean | smooth_iff_pullback_preserves_smooth_real_functions 等 | new | Manifold/SmoothFunctionCriterion | 是 | 回拉保光滑函数判据有用，定理全 sorry |
| Sec02_12/Problem_2_11.lean | Projectivization.basisMap, BasisCompatible 等 | new | Instances/Projectivization | 是 | Projectivization 结构搬运层，关键证明 sorry 且依赖一章 |
| Sec02_12/Problem_2_13.lean | paracompactSpace_of_hasSubordinatePartitionOfUnity | new | Manifold/PartitionOfUnity | 否 | 单位分解⇒仿紧逆向全证，Mathlib 仅有正向 |
| Sec02_12/Problem_2_6.lean | projectivizationMap, contMDiff_projectivizationMap 等 | new | Manifolds/ProjectiveSpace | 否 | 齐次映射下降到 ℝPⁿ 为新，需先移项目图册 |
| Sec02_12/Problem_2_7.lean | smooth_functions_not_finiteDimensional 等 | new | Util/SmoothFunctionSpace | 否 | C^∞(M,ℝ) 无限维全证，于本库方向偏小众 |
| Sec02_08/Corollary_2_8.lean | gluing_lemma_for_smooth_maps | partial-dup | Manifold/SmoothManifold | 否 | 光滑层粘合解包为 ContMDiff 级可用陈述 |
| Sec02_08/Exercise_2_2.lean | contMDiff_open_submanifold_halfspace_iff_forall_exists_smoothAmbientExtension 等 | partial-dup | Manifold/Boundary | 否 | 半空间延拓判据真缺，需连带一章依赖文件 |
| Sec02_09/Theorem_2_18.lean | Diffeomorph.restrictInterior 等 | partial-dup | Manifold/Diffeomorph | 是 | 限制到流形内部为新，依项目内设施且 simp 引理 sorry |
| Sec02_11/Proposition_2_25.lean | exists_smooth_bump_function_for | partial-dup | Manifold/BumpFunction | 否 | 严格 tsupport⊆U 闭集 bump，可扩展本库模块 |
| Sec02_12/Problem_2_3.lean | hopf_map, hopf_map_smooth 等 | partial-dup | Instances/HopfFibration | 是 | Hopf 映射 S³→S² 为新典型例，五条证明全 sorry |

</details>

<details><summary>跳过（40 项，绝大多数为 Mathlib 包装/recall 文件）</summary>

- Sec02_08/Definition_2_8_extra_2.lean — mathlib-dup — 纯 #check 复述
- Sec02_08/Definition_2_8_extra_4.lean — mathlib-dup — 薄逐点推论
- Sec02_08/Definition_2_8_extra_5.lean — mathlib-dup — recall 编号对照
- Sec02_08/Definition_2_8_extra_6.lean — partial-dup — 既有 API 已覆盖
- Sec02_08/Exercise_2_1.lean — mathlib-dup — 仅 #check 环结构
- Sec02_08/Exercise_2_11.lean — mathlib-dup — 三条 recall
- Sec02_08/Exercise_2_3.lean — mathlib-dup — 两行包装
- Sec02_08/Exercise_2_7.lean — mathlib-dup — 纯 recall 交叉引用
- Sec02_08/Exercise_2_9.lean — mathlib-dup — 四行包装
- Sec02_08/Notation_2_8_extra_3.lean — mathlib-dup — 记号对照 #check
- Sec02_08/Proposition_2_10.lean — mathlib-dup — 四条 #check
- Sec02_08/Proposition_2_4.lean — mathlib-dup — 单条 #check
- Sec02_08/Proposition_2_5.lean — mathlib-dup — 单条 #check
- Sec02_08/Proposition_2_6.lean — mathlib-dup — 两条 #check
- Sec02_08/Remark_2_8_extra_1.lean — new — 术语谓词无数学内容
- Sec02_08/Remark_2_8_extra_7.lean — mathlib-dup — 零声明词汇复述
- Sec02_09/Definition_2_9_extra_1.lean — mathlib-dup — 纯 #check
- Sec02_09/Exercise_2_16.lean — partial-dup — recall 脚手架
- Sec02_09/Exercise_2_19.lean — partial-dup — recall 脚手架
- Sec02_10/Definition_2_10_extra_1.lean — mathlib-dup — 文档加单 #check
- Sec02_10/Definition_2_10_extra_2.lean — mathlib-dup — 本库已有包装
- Sec02_10/Definition_2_10_extra_3.lean — mathlib-dup — 定义 recall
- Sec02_10/Definition_2_10_extra_4.lean — mathlib-dup — 定义 recall
- Sec02_10/Exercise_2_24.lean — mathlib-dup — #check 特化
- Sec02_10/Lemma_2_20.lean — mathlib-dup — recall 指针
- Sec02_10/Lemma_2_21.lean — partial-dup — smoothStep 已覆盖
- Sec02_10/Lemma_2_22.lean — partial-dup — ContDiffBump 已供
- Sec02_10/Theorem_2_23.lean — mathlib-dup — sorry 复述
- Sec02_11/Definition_2_11_extra_1.lean — new — 平凡常函数检查
- Sec02_11/Exercise_2_27.lean — new — 教学反例
- Sec02_11/Theorem_2_29.lean — mathlib-dup — 六行特化包装
- Sec02_12/Problem_2_1.lean — new — 教学反例无 API
- Sec02_12/Problem_2_12.lean — new — 主定理单 sorry
- Sec02_12/Problem_2_14.lean — mathlib-dup — 字面 recall
- Sec02_12/Problem_2_5.lean — new — 教材特定含两 sorry
- Sec02_12/Problem_2_8.lean — new — 依赖未移植图册
- Sec02_12/Problem_2_9.lean — new — 教材特定大量辅件
- Sec02_12/Problem_2_9_corecheck.lean — new — 流水线快照
- Sec02_12/Problem_2_9_pre_north.lean — new — 流水线快照
- Sec02_12/Problem_2_9_prefixcheck.lean — new — 流水线快照

</details>

## 小结

第二章共审计 55 个文件，其中大部分（约 40 个）是对 Mathlib 既有 ContMDiff / 光滑函数 / 单位分解 API 的 #check 或 recall 式复述，可直接跳过。真正值得移植的核心资产集中在两条线：一是 Diffeomorph 基础设施（乘积、开子流形限制、维数不变性、单位球与图卡的打包微分同胚），二是闭球带边流形构造（Problem 2.4，2600 行无 sorry）与正光滑穷竭函数（Proposition 2.28），后两者直接支撑 GMT 散度定理与非紧 L²/Bochner 方向的缺口。中等价值项多数围绕光滑延拓、投影空间结构与回拉判据，部分仍含 sorry，宜在对应目标模块成型后按依赖顺序择机引入。

---

# Chap03

## 移植优先（high，4 项）

| 文件 | 声明 | 分类 | 落点 | sorry | 理由 |
|---|---|---|---|---|---|
| Sec03_14/Proposition_3_9.lean | mfderiv_open_subset_inclusion_isInvertible | new | Util/Tangent | 否 | 开子集包含微分可逆全证，Mathlib 缺此切空间识别 API |
| Sec03_17/Proposition_3_23.lean | exists_smooth_curve_with_velocity, exists_smooth_curve_with_velocity_boundaryless 等 | new | CurveVelocity | 否 | 曲线速度满射切空间含边界情形，Mathlib 全缺 |
| Sec03_16/Proposition_3_20.lean | tangent_bundle_opens_trivializationAt_eq_toProd, globalChartDiffeomorph 等 | partial-dup | TangentBundle/Trivialization | 否 | 单图卡切丛平凡化全证，主 def 依赖含 sorry 的 3.22 |
| Sec03_20/Problem_3_7.lean | TangentSpace.toPointDerivation, smooth_germ_derivation_existsUnique_tangentVector 等 | partial-dup | TangentBundle/PointDerivation | 是 | 切向量≃芽导子等价，Mathlib 著名缺口，余两条 sorry |

<details><summary>可考虑（medium，11 项）</summary>

| 文件 | 声明 | 分类 | 落点 | sorry | 理由 |
|---|---|---|---|---|---|
| Sec03_13/Proposition_3_2.lean | directional_point_derivation, geometric_to_point_derivation_linear_equiv 等 | new | Util/Tangent/PointDerivation | 是 | 几何切向量↔导子等价是真缺口，但仅欧氏且关键步全 sorry |
| Sec03_14/Lemma_3_11.lean | mfderiv_half_space_inclusion_isInvertible_of_boundary_eq_zero | new | Manifold/Boundary | 是 | 半空间包含边界点微分可逆，仅语句无证明可移 |
| Sec03_14/Proposition_3_8.lean | PointDerivation.congr_of_eqOn_nhds | new | Manifold/Derivation | 否 | 导子局部性 bump 函数完整证明，但本库不用导子模型 |
| Sec03_17/Definition_3_17_extra_1.lean | curve_velocity, curve_velocityWithin 等 | new | CurveVelocity | 否 | 命名曲线速度薄封装，是移植 3.23 的基础 |
| Sec03_18/Definition_3_18_extra_3.lean | SmoothCurveAt, CurveVelocityClass 等 | new | TangentBundle/CurveVelocity | 是 | 曲线速度实现切空间，两核心定理 sorry 需重设计 |
| Sec03_18/Definition_3_18_extra_4.lean | IsCoordinateTangentVector, TangentSpace.coordinateComponent 等 | new | TangentBundle/CoordinateComponents | 否 | 坐标分量 API 全证，Mathlib 缺，偏教学起源 |
| Sec03_20/Problem_3_4.lean | tangentBundle_circle_diffeomorph_prodLie, circleTangentFiberDiffeomorph 等 | new | TangentBundle/LieGroupTrivialization | 否 | 李群平凡化 TG≃G×Lie(G) 全证，硬编码圆需泛化 |
| Sec03_14/Proposition_3_6.lean | mfderiv_comp_of_smooth, diffeomorph_mfderiv_symm_eq_symm | partial-dup | Util/Tangent | 否 | 微分同胚逆的微分等于微分之逆，Mathlib 缺的小胶水 |
| Sec03_15/Proposition_3_15.lean | chart_mdifferentiable_of_mem_maximalAtlas, chart_coordinate_vectors_basis | partial-dup | Util/Chart/CoordinateBasis | 否 | 图卡 mfderiv 打包成 Basis，小型可复用坐标 API |
| Sec03_16/Corollary_3_22.lean | tangentMap_diffeomorph, tangentMap_comp_of_smooth 等 | partial-dup | TangentBundle/Diffeomorph | 是 | Diffeomorph 诱导切丛微分同胚，五条辅助引理 sorry |
| Sec03_20/Problem_3_1.lean | isLocallyConstant_of_mfderiv_eq_zero, mfderiv_eq_zero_iff_isLocallyConstant 等 | partial-dup | TangentBundle/MFDerivLocallyConstant | 是 | mfderiv≡0 当且仅当局部常值，正向 sorry 受阻 |

</details>

<details><summary>跳过（42 项，绝大多数为 Mathlib 包装/recall 文件）</summary>

- Sec03_13/Corollary_3_3.lean — new — 欧氏限定全 sorry
- Sec03_13/Definition_3_13_extra_1.lean — mathlib-dup — 薄包装加记号
- Sec03_13/Definition_3_13_extra_2.lean — mathlib-dup — 仅 #check 复述
- Sec03_13/Definition_3_13_extra_3.lean — mathlib-dup — rfl 级复述
- Sec03_13/Exercise_3_5.lean — mathlib-dup — 纯 #check 回顾
- Sec03_13/Lemma_3_1.lean — mathlib-dup — 欧氏一行推论
- Sec03_13/Lemma_3_4.lean — mathlib-dup — 一行包装
- Sec03_14/Definition_3_14_extra_1.lean — mathlib-dup — 复述 mfderiv 签名
- Sec03_14/Definition_3_14_extra_2.lean — mathlib-dup — 单个 #check
- Sec03_14/Exercise_3_7.lean — mathlib-dup — 纯 #check 复述
- Sec03_14/Proposition_3_10.lean — mathlib-dup — 一行 defeq
- Sec03_14/Proposition_3_12.lean — mathlib-dup — sorry 复述维数
- Sec03_14/Proposition_3_13.lean — mathlib-dup — 一行包装附 sorry
- Sec03_15/Definition_3_15_extra_1.lean — partial-dup — 已被现有 API 覆盖
- Sec03_15/Definition_3_15_extra_2.lean — partial-dup — 一行 .repr 包装
- Sec03_15/Example_3_16.lean — new — 教科书数值例
- Sec03_15/Exercise_3_17.lean — new — 教学专用示例
- Sec03_15/Remark_3_15_extra_3.lean — mathlib-dup — 纯回顾
- Sec03_15/Remark_3_15_extra_4.lean — partial-dup — 两行胶水已有
- Sec03_15/Remark_3_15_extra_5.lean — mathlib-dup — 回顾复述
- Sec03_16/Definition_3_16_extra_1.lean — mathlib-dup — 回顾 TangentBundle
- Sec03_16/Definition_3_16_extra_3.lean — mathlib-dup — 仅 #check
- Sec03_16/Exercise_3_19.lean — new — 单个 rfl 定理
- Sec03_16/Notation_3_16_extra_2.lean — mathlib-dup — 仅记号加 #check
- Sec03_16/Notation_3_16_extra_4.lean — mathlib-dup — 回顾桥引理
- Sec03_16/Proposition_3_18.lean — mathlib-dup — 特化 contMDiff_proj
- Sec03_16/Proposition_3_21.lean — mathlib-dup — 单个 #check 特化
- Sec03_17/Proposition_3_24.lean — mathlib-dup — 链规则一行求值
- Sec03_17/Corollary_3_25.lean — mathlib-dup — 复述 3.24
- Sec03_18/Definition_3_18_extra_1.lean — mathlib-dup — 记号加一行实例
- Sec03_18/Definition_3_18_extra_2.lean — partial-dup — 平凡 abbrev 加 sorry
- Sec03_19/Definition_3_19_extra_1.lean — mathlib-dup — 回顾 Category
- Sec03_19/Definition_3_19_extra_2.lean — mathlib-dup — 回顾 IsIso
- Sec03_19/Definition_3_19_extra_3.lean — mathlib-dup — 回顾小范畴概念
- Sec03_19/Definition_3_19_extra_4.lean — mathlib-dup — 仅 #check 函子
- Sec03_19/Definition_3_19_extra_5.lean — mathlib-dup — 仅 #check 反变函子
- Sec03_19/Example_3_26.lean — partial-dup — 教学示例
- Sec03_19/Exercise_3_27.lean — mathlib-dup — 回顾无新证明
- Sec03_20/Problem_3_3.lean — mathlib-dup — 纯回顾复述
- Sec03_20/Problem_3_5.lean — new — 教科书专用习题
- Sec03_20/Problem_3_6.lean — new — 具体例几乎全 sorry
- Sec03_20/Problem_3_8.lean — new — 纯回顾桥文件

</details>

## 小结

第三章共审计 53 个文件，其中约四分之三为 Mathlib 重复（recall/#check 复述或一行包装），可直接跳过。真正值得移植的高价值条目集中在切空间基础设施：开子集包含映射微分可逆性（Proposition 3.9）、曲线速度满射（Proposition 3.23）、单图卡切丛平凡化（Proposition 3.20）以及切向量-导子等价（Problem 3.7），前三者中两个已完全无 sorry。中价值条目多围绕导子模型与坐标基 API，但普遍含 sorry 或需要设计返工，建议在 CurveVelocity 与 Tangent 工具模块落地高价值条目后再酌情跟进。

---

# Chap04

## 移植优先（high，16 项）

| 文件 | 声明 | 分类 | 落点 | sorry | 理由 |
|---|---|---|---|---|---|
| Sec04_21/Exercise_4_3.lean | prod_fst_isSmoothSubmersion, prod_mk_right_isImmersion 等 | new | Manifold/ImmersionSubmersion | 否 | 积投影淹没/切片浸入全证，含可复用图卡群胚基建 |
| Sec04_21/Exercise_4_4.lean | IsSmoothSubmersion.comp, IsImmersion.comp 等 | new | Manifold/ImmersionSubmersion | 是 | 淹没复合与秩 API，攻 Mathlib TODO，一辅助引理 3 sorry |
| Sec04_22/Proposition_4_8.lean | IsLocalDiffeomorph.isImmersion, is_local_diffeomorph_iff_is_immersion_and_is_smooth_submersion 等 | new | Manifold/Submersion | 否 | 局部微分同胚↔浸入+淹没全证，上游谓词含 sorry |
| Sec04_22/Theorem_4_5.lean | isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible, model_partialDiffeomorph_of_inverse_function_theorem 等 | new | Manifold/InverseFunctionTheorem | 否 | 流形版反函数定理完整证明，Mathlib 明确 TODO |
| Sec04_24/Exercise_4_16.lean | IsImmersion.ex416_comp, IsSmoothEmbedding.comp 等 | new | SmoothManifold/Immersion | 是 | 浸入/光滑嵌入复合，Mathlib proof_wanted，余一 sorry |
| Sec04_25/Definition_4_25_extra_2.lean | Topology.IsTopologicalSubmersion, IsTopologicalSubmersion.isQuotientMap 等 | new | Manifold/Submersion | 否 | 拓扑淹没 API 全证（开/商映射），Mathlib 缺 |
| Sec04_25/Proposition_4_28.lean | Manifold.IsSmoothSubmersion, IsSmoothSubmersion.isOpenMap 等 | new | Manifold/Submersion | 否 | 定义 Mathlib 缺失的光滑淹没结构，依赖含 sorry 的 4.26 |
| Sec04_25/Theorem_4_26.lean | Manifold.IsSmoothLocalSection, smooth_submersion_iff_exists_smooth_local_section_through_every_point 等 | new | Manifold/Submersion | 是 | 局部截面定理刻画淹没，主定理 sorry 需秩定理级工作 |
| Sec04_25/Theorem_4_29.lean | Manifold.contMDiff_iff_comp_of_surjective_smooth_submersion | new | Manifold/Submersion | 是 | 满淹没特征性质是商流形主力引理，仅语句含 sorry |
| Sec04_25/Theorem_4_30.lean | Manifold.existsUnique_contMDiff_lift_of_surjective_smooth_submersion | new | Manifold/Submersion | 是 | 商流形光滑提升存在唯一性核心基建，证明为 sorry |
| Sec04_26/Definition_4_26_extra_1.lean | Manifold.IsSmoothCoveringMap, IsUniversalSmoothCoveringMap 等 | new | Manifold/CoveringMap | 否 | 光滑覆盖映射核心定义层，Mathlib 仅有拓扑版 |
| Sec04_26/Exercise_4_37.lean | IsLocalDiffeomorph.isSmoothLocalSection, IsSmoothCoveringMap.isSmoothLocalSection 等 | new | Manifold/CoveringMap | 否 | 连续局部截面自动光滑，全证通用升级引理 |
| Sec04_26/Proposition_4_36.lean | IsCoveringMap.exists_localSectionOn, IsSmoothCoveringMap.localSection_eq 等 | new | Manifold/CoveringMap | 否 | 光滑局部截面存在与预连通集上唯一性，完整 API |
| Sec04_26/Proposition_4_40.lean | exists_unique_smooth_covering_structure, lifted_covering_chartedSpace 等 | new | Manifold/CoveringMap | 否 | 拓扑覆盖唯一光滑结构，700 行无 sorry 大定理 |
| Sec04_26/Proposition_4_46.lean | isSmoothCoveringMap_of_proper_localDiffeomorph, fiber_finite_of_proper_local_diffeomorph 等 | new | Manifold/CoveringMap | 否 | 真局部微分同胚⇒覆盖映射判据全证，移植需并回正式定义 |
| Sec04_27/Problem_4_5.lean | complexProjectiveQuotientMap_isSmoothSubmersion, complexProjectiveLine_diffeomorphic_sphere 等 | new | Instances/ComplexProjectiveSpace | 否 | CP^n 商淹没全证，含 CP^1≅S^2 压轴构造 |

<details><summary>可考虑（medium，22 项）</summary>

| 文件 | 声明 | 分类 | 落点 | sorry | 理由 |
|---|---|---|---|---|---|
| Sec04_21/Definition_4_21_extra_1.lean | rank_at_eq_finrank_range_mfderiv, is_immersion_iff_forall_injective_mfderiv 等 | new | Manifold/Rank | 是 | 秩 API 填 Mathlib 缺口，但定理全 sorry 仅语句可移 |
| Sec04_21/Proposition_4_1.lean | exists_open_restriction_isSmoothSubmersion_of_surjective_mfderiv, exists_open_restriction_isImmersion_of_injective_mfderiv | new | Manifold/ImmersionSubmersion | 是 | 点态满/单 mfderiv 给局部淹没/浸入，证明全 sorry |
| Sec04_22/Exercise_4_10.lean | smooth_iff_comp_left_of_isLocalDiffeomorph, smooth_iff_comp_right_of_surjective_isLocalDiffeomorph | new | Manifold/LocalDiffeomorph | 否 | 经局部微分同胚前后复合检测光滑性，全证 iff 引理 |
| Sec04_23/Theorem_4_14.lean | constant_rank_surjective_is_smooth_submersion, constant_rank_injective_is_immersion 等 | new | Manifold/RankTheorem | 是 | 全局秩定理是真缺口，但三证明全 sorry 仅语句 |
| Sec04_23/Theorem_4_15.lean | boundary_immersion_normal_form, BoundaryLocalCoordinateNormalFormAt 等 | new | Manifold/Boundary | 是 | 带边流形浸入边界标准形，与 GMT 相关但主定理 sorry |
| Sec04_24/Definition_4_24_extra_2.lean | Topology.IsTopologicalImmersion, IsEmbedding.isTopologicalImmersion 等 | new | SmoothManifold/Immersion | 否 | 局部嵌入谓词小型全证拓扑 API，单独价值有限 |
| Sec04_24/Proposition_4_22.lean | smooth_embedding_of_injective_isImmersion_isOpenMap, smooth_embedding_of_compact_source_injective_isImmersion 等 | new | SmoothManifold/Embedding | 是 | 单浸入成嵌入的充分条件骨架，五证明全 sorry |
| Sec04_24/Theorem_4_25.lean | Manifold.isImmersion_iff_forall_exists_open_restriction_isSmoothEmbedding | new | SmoothManifold/Embedding | 是 | 局部嵌入定理是真缺口，但仅单条 sorry 存根 |
| Sec04_25/Definition_4_25_extra_1.lean | ContinuousMap.IsLocalSection, Function.RightInverse.isLocalSection_restrict_top 等 | new | Manifold/Submersion | 否 | 连续映射局部截面谓词，小而全证的基础层 |
| Sec04_25/Theorem_4_31.lean | Manifold.existsUnique_diffeomorph_of_surjective_smooth_submersions_constant_on_each_others_fibers | new | Manifold/Submersion | 是 | 光滑商唯一性，4.29/4.30 的推论，仅语句 sorry |
| Sec04_26/Exercise_4_38.lean | Manifold.IsSmoothCoveringMap.pi, isCoveringMap_pi 等 | new | Manifold/CoveringMap | 否 | 覆盖映射有限积定理无 sorry，移植前需精简同胚管线 |
| Sec04_26/Exercise_4_39.lean | Bundle.Trivialization.sheet_coordinate_eq_on_component, component_bijOn_baseSet 等 | new | Manifold/CoveringMap | 否 | 叶分解引理全证，Mathlib 缺的 Trivialization API，略偏门 |
| Sec04_26/Proposition_4_33.lean | IsSmoothCoveringMap.isSmoothSubmersion, diffeomorphOfInjective 等 | new | Manifold/CoveringMap | 是 | 覆盖映射基本性质接口正确，但五条中四条 sorry |
| Sec04_27/Problem_4_11.lean | isProperMap_iff_finite_fibers_of_isCoveringMap, exists_smoothCoveringMap_not_isProperMap | new | MetricGeometry/Covering/ProperMap | 是 | 覆盖真当且仅当纤维有限是真缺口，仅语句需从头证 |
| Sec04_27/Problem_4_12.lean | torus_of_revolution_map_isSmoothEmbedding, torus_product_isManifold 等 | new | Instances/Torus | 否 | 平坦环面嵌入 R^3 全证，含 pi 群胚/积流形助手 |
| Sec04_27/Problem_4_3.lean | boundary_rank_normal_form, constant_rank_boundary_local_coordinate_normal_form | new | Manifold/RankTheorem | 是 | 边界点常秩标准形是真缺口，但 sorry 语句且形式别扭 |
| Sec04_27/Problem_4_6.lean | not_exists_smooth_submersion_to_euclideanSpace | new | Manifold/Submersion | 否 | 紧流形无淹没到 R^k 经典结果全证，依赖项目谓词 |
| Sec04_27/Problem_4_7.lean | contMDiff_iff_comp_equiv_of_submersion_characteristic_property, exists_diffeomorph_of_submersion_characteristic_property | new | Manifold/Submersion | 是 | 商光滑结构唯一性有价值，但两定理皆 sorry |
| Sec04_22/Proposition_4_6.lean | isLocalDiffeomorph_comp, isLocalDiffeomorph_pi 等 | partial-dup | Manifold/LocalDiffeomorph | 是 | 缺失的复合/积/坐标判据引理全 sorry，余为回顾 |
| Sec04_23/Theorem_4_12.lean | rank_normal_form, constant_rank_local_coordinate_normal_form 等 | partial-dup | Manifold/RankTheorem | 是 | 常秩定理是真缺口，但五证明全 sorry 且欧氏结构需重构 |
| Sec04_24/Example_4_20.lean | denseTorusCurve, circle_exp_isLocalDiffeomorph_from_angle_branch 等 | partial-dup | SmoothManifold/CircleExp | 否 | 无理缠绕属反例，Circle.exp 局部微分同胚助手可复用 |
| Sec04_26/Example_4_35.lean | circle_exp_isSmoothCoveringMap, sphere_to_realProjectiveSpace_isCoveringMap 等 | partial-dup | Instances/CoveringExamples | 否 | 光滑覆盖实例全证，RP^n 覆盖为新内容好例证 |

</details>

<details><summary>跳过（26 项，绝大多数为 Mathlib 包装/recall 文件）</summary>

- Sec04_21/Example_4_2.lean — new — 全 sorry 教学例
- Sec04_22/Definition_4_22_extra_1.lean — mathlib-dup — 纯 abbrev 复述
- Sec04_22/Exercise_4_7.lean — mathlib-dup — 仅 #check 回顾
- Sec04_22/Exercise_4_9.lean — new — 欧氏硬编码加 sorry
- Sec04_23/Corollary_4_13.lean — new — 单条 sorry 复述
- Sec04_24/Definition_4_24_extra_1.lean — mathlib-dup — 八行仅 #check
- Sec04_24/Example_4_17.lean — partial-dup — of_opens 加 sorry 存根
- Sec04_24/Example_4_18.lean — new — 单个具体反例
- Sec04_24/Example_4_19.lean — new — 教学八字曲线反例
- Sec04_24/Exercise_4_24.lean — new — 一次性反例机件
- Sec04_24/Lemma_4_21.lean — mathlib-dup — 重证 Dirichlet 逼近
- Sec04_25/Exercise_4_27.lean — new — x^3 教学反例
- Sec04_25/Exercise_4_32.lean — new — 纯回顾 4.31
- Sec04_26/Corollary_4_43.lean — new — sorry 存根
- Sec04_26/Exercise_4_34.lean — new — 纯回顾脚手架
- Sec04_26/Exercise_4_42.lean — new — 纯回顾 4.41
- Sec04_26/Exercise_4_44.lean — new — 纯回顾 4.43
- Sec04_26/Exercise_4_45.lean — new — 边界框架 sorry 存根
- Sec04_26/Proposition_4_41.lean — new — 边界版主结果全 sorry
- Sec04_27/Problem_4_1.lean — new — 薄包装单反例
- Sec04_27/Problem_4_10.lean — new — 单条 sorry 语句
- Sec04_27/Problem_4_13.lean — new — 语句依赖未证基建
- Sec04_27/Problem_4_2.lean — mathlib-dup — 一行特化
- Sec04_27/Problem_4_4.lean — new — 纯记账回顾
- Sec04_27/Problem_4_8.lean — new — 全 sorry 反例
- Sec04_27/Problem_4_9.lean — new — 纯回顾视图

</details>

## 小结

第四章（浸入、淹没、嵌入与覆盖映射）是整个审计中移植价值最高的章节之一：16 个高价值文件中多数完全无 sorry，包括流形版反函数定理（Mathlib 明确 TODO）、光滑淹没与光滑覆盖映射的完整定义层 API、拓扑覆盖提升唯一光滑结构的 700 行大定理，以及 CP^n 商淹没与 CP^1 ≅ S^2 的完整构造。中价值条目主要是设计良好但证明缺失的语句骨架（秩定理、全局秩定理、商流形特征性质），移植它们等于承诺补全秩定理级别的证明工作。建议优先按 Submersion → CoveringMap → InverseFunctionTheorem 的依赖顺序成块移植无 sorry 文件，再以其为基础逐步补证 IsSmoothSubmersion 上游的局部截面定理。

---

# Chap05

## 移植优先（high，18 项）

| 文件 | 声明 | 分类 | 落点 | sorry | 理由 |
|---|---|---|---|---|---|
| Sec05_28/Definition_5_28_extra_1.lean | IsEmbeddedSubmanifold、IsEmbeddedSubmanifold.codimension 等 | new | Manifold/Submanifold/Embedded | 否 | 嵌入子流形类填 Mathlib 空白，需 Sec05_31 浸入结构 |
| Sec05_28/Proposition_5_4.lean | graphMap、graphMap_isSmoothEmbedding 等 | new | Manifold/Submanifold/Graph | 是 | 光滑映射的图作光滑嵌入，Mathlib 缺，GMT 基础 |
| Sec05_29/Definition_5_29_extra_1.lean | Set.euclideanSlice、Set.IsSliceInChart 等 | new | Manifold/SliceCharts | 否 | 切片图卡/局部切片条件 API，子流形理论根基 |
| Sec05_29/Theorem_5_8.lean | local_slice_criterion_for_embedded_submanifold 等 | new | Manifold/SliceCharts | 否 | 局部 k-切片判据无 sorry 全证，Mathlib 空白 |
| Sec05_30/Proposition_5_16.lean | euclidean_tail_projection、embedded_submanifold_iff_locally_level_set_of_smooth_submersion 等 | new | Manifold/Submanifold/LocalDefining | 是 | 浸没水平集局部判据，投影引理已证，主 iff 仍 sorry |
| Sec05_31/Definition_5_31_extra_1.lean | Manifold.ImmersedSubmanifold、IsImmersion.toImmersedSubmanifold 等 | new | Manifold/Submanifold/Immersed | 否 | 无 sorry 捆绑浸入子流形结构，varifold 代码直接受益 |
| Sec05_32/Corollary_5_30.lean | IsSmoothEmbedding.contMDiff_toSubtype、contMDiffAt_toSubtype 等 | new | Manifold/Submanifold | 否 | 一般余域限制定理已证，Mathlib 仅有球面特例 |
| Sec05_35/Corollary_5_39.lean | tangent_iff_mfderiv_eq_zero_of_isDefiningFunction 等 | new | Submanifold/LevelSet | 否 | 正则值切空间刻画已证，但依赖含 sorry 的命题 5.38 |
| Sec05_35/Definition_5_35_extra_2.lean | IsInwardPointing、IsBoundaryTangentVector 等 | new | Boundary/PointingVectors | 否 | 内外指向向量 API 填散度定理缺口，定义需重设计 |
| Sec05_35/Notation_5_35_extra_1.lean | Manifold.submanifoldTangentSpace、T[J; p] 记号 | new | Submanifold/TangentSpace | 否 | 子流形切空间核心定义，全节定理之基石 |
| Sec05_35/Proposition_5_35.lean | tangentVector_mem_submanifold_iff_exists_curve 等 | new | Submanifold/TangentSpace | 否 | 切向量即曲线速度，全证，需 Chap03 曲线基建 |
| Sec05_35/Proposition_5_38.lean | IsLocalDefiningMapOn、tangentSpace_eq_ker_mfderiv_of_isLocalDefiningMapOn | new | Submanifold/LevelSet | 是 | 局部定义映射核心 API，5.39/5.40 依赖，主定理 sorry |
| Sec05_36/Definition_5_36_extra_4.lean | Set.euclideanHalfSlice、OpenPartialHomeomorph.IsBoundarySliceChart 等 | new | Manifold/SliceCharts | 否 | 带边界半切片图卡 API 无 sorry，需 Sec05_29 配套 |
| Sec05_36/Theorem_5_51.lean | local_slice_criterion_for_embedded_submanifold_with_boundary 等 | new | Manifold/SubmanifoldWithBoundary | 是 | 带边界 k-切片判据约 2000 行，核心三处 sorry 待补 |
| Sec05_37/Problem_5_18.lean | immersed_submanifold_isEmbeddedSubmanifold_iff_smoothFunctions_isSmoothOn 等 | new | Manifold/Submanifold/SmoothExtension | 否 | 嵌入 iff 光滑函数可延拓，无 sorry 可复用 API |
| Sec05_37/Problem_5_23.lean | IsBoundaryRegularValue、regular_preimage_has_embedded_submanifold_with_boundary_structure 等 | new | Manifold/Submanifold/RegularValue | 是 | 带边界正则值原像定理大部已证，余两引理 sorry |
| Sec05_37/Problem_5_8.lean | basis_model_diffeomorph、regularCoordinateBall_compl_boundary_diffeomorph_sphere 等 | new | Manifold/CoordinateBall | 是 | 正则坐标球/正则域基建近完成，仅余一处 sorry |
| Sec05_36/Proposition_5_49.lean | isSmoothEmbedding_of_le、immersed_submanifold_has_embedded_neighborhood 等 | partial-dup | Manifold/Submanifold | 否 | 嵌入像诱导结构已证，超出 Mathlib SmoothEmbedding |

<details><summary>可考虑（medium，33 项）</summary>

| 文件 | 声明 | 分类 | 落点 | sorry | 理由 |
|---|---|---|---|---|---|
| Sec05_28/Proposition_5_2.lean | IsInducedImageManifoldStructure、smooth_embedding_range_has_induced_manifold_structure 等 | new | Manifold/Submanifold/InducedStructure | 是 | 像上诱导结构是基石，但定理全 sorry 且 API 需重做 |
| Sec05_28/Proposition_5_3.lean | productSliceMap、productSliceMap_isSmoothEmbedding 等 | new | Manifold/Submanifold/Product | 是 | 切片嵌入 x↦(x,p) 小引理可用，主定理全 sorry |
| Sec05_28/Proposition_5_7.lean | smooth_map_graph_isProperlyEmbedded | new | Manifold/Submanifold/Graph | 是 | 全局图真嵌入，单条 sorry，应与命题 5.4 同移植 |
| Sec05_29/Exercise_5_10.lean | sphericalCoordinates、sphericalCoordinates_mem_maximalAtlas 等 | new | Instances/SphericalCoordinates | 否 | 三维球坐标图卡全证，但属具体图卡非通用基建 |
| Sec05_30/Corollary_5_13.lean | smooth_submersion_level_set_has_embedded_submanifold_structure 等 | new | Manifold/Submanifold/LevelSet | 否 | 浸没水平集推论为薄包装，依赖含 sorry 定理 5.12 |
| Sec05_30/Corollary_5_14.lean | regular_level_set_has_embedded_submanifold_structure 等 | new | Manifold/Submanifold/LevelSet | 是 | 正则水平集定理填空白，但全 sorry 需从头证 |
| Sec05_30/Definition_5_30_extra_2.lean | Manifold.IsRegularPoint、Manifold.IsCriticalValue 等 | new | Manifold/Submanifold/RegularValue | 是 | 正则/临界点词汇缺失，但支撑引理全 sorry |
| Sec05_30/Definition_5_30_extra_3.lean | Set.IsDefiningMap、Set.IsLocalDefiningMapOn 等 | new | Manifold/Submanifold/DefiningMap | 是 | 定义映射 API 空白，但类设计需大幅重做 |
| Sec05_30/Theorem_5_12.lean | constant_rank_level_set_has_embedded_submanifold_structure 等 | new | Manifold/Submanifold/LevelSet | 是 | 常秩水平集定理为关键空白，全 sorry 仅语句可移 |
| Sec05_31/Definition_5_31_extra_2.lean | ImmersedSubmanifold.IsLocalParametrization、IsGlobalParametrization 等 | new | Manifold/Submanifold/Parametrization | 是 | 参数化谓词新颖，但硬编码 Fin k，API 需重做 |
| Sec05_31/Exercise_5_20.lean | ImmersedSubmanifold.continuous_inclusion、subspaceTopology_le_givenTopology_iff_isEmbedding 等 | new | Manifold/Submanifold/Immersed | 否 | 已证核心 API，应与 Definition_5_31_extra_1 同移植 |
| Sec05_31/Proposition_5_18.lean | injective_immersion_range_has_immersed_submanifold_structure 等 | new | Manifold/Submanifold/Immersed | 是 | 单射浸入像结构存在唯一性，仅语句无证明 |
| Sec05_31/Proposition_5_22.lean | ImmersedSubmanifold.exists_open_neighborhood_isSmoothEmbedding | new | Manifold/Submanifold/Immersed | 是 | 浸入子流形局部嵌入有用，但全文单条 sorry 语句 |
| Sec05_31/Proposition_5_23.lean | IsImmersion.isSmoothLocalParametrization_of_mem_maximalAtlas 等 | new | Manifold/Submanifold/Parametrization | 否 | 图卡给局部参数化已证，但绑定待重做的定义 |
| Sec05_32/Remark_5_32_extra_1.lean | IsWeaklyEmbeddedSubmanifold 实例 | new | Manifold/Submanifold | 否 | 嵌入蕴含弱嵌入的胶水实例，须随子流形类同移 |
| Sec05_32/Theorem_5_29.lean | contMDiff_toSubtype_of_isImmersedSubmanifold | new | Manifold/Submanifold | 是 | 推广推论 5.30 的余域限制，仅语句需从头证 |
| Sec05_33/Theorem_5_31.lean | immersed_submanifold_structure_unique_of_same_carrier | new | Manifold/Submanifold | 是 | 子流形结构唯一性 sorry 语句，需全套 API 加真证明 |
| Sec05_35/Definition_5_35_extra_3.lean | BoundaryDefiningFunction、CoeFun 实例 | new | Boundary/DefiningFunction | 否 | 捆绑边界定义函数，硬编码半空间且与 5.43 重复 |
| Sec05_35/Exercise_5_40.lean | tangentSpace_eq_ker_mfderiv_of_level_set_of_hasConstantRank 等 | new | Submanifold/LevelSet | 是 | 常秩水平集切空间，关键引理 sorry 且与 5.39 重复 |
| Sec05_35/Exercise_5_44.lean | boundary_defining_derivative、inwardPointing_iff_boundaryDefiningDerivative_pos 等 | new | Boundary/DefiningFunction | 是 | 导数符号刻画内外向是对的 API，四定理全 sorry |
| Sec05_35/Proposition_5_37.lean | tangentVector_mem_submanifold_iff_forall_smooth_eq_zero | new | Submanifold/TangentSpace | 是 | 函数式切向刻画，单条 sorry，证明需延拓引理 |
| Sec05_35/Proposition_5_41.lean | boundary_coordinate_component、boundary_vector_trichotomy 等 | new | Boundary/PointingVectors | 是 | 边界向量坐标三分法配套定理，八条全 sorry |
| Sec05_35/Proposition_5_43.lean | IsBoundaryDefiningFunction、exists_boundary_defining_function | new | Boundary/DefiningFunction | 是 | 全局边界定义函数存在性 sorry，与 extra_3 重复 |
| Sec05_36/Definition_5_36_extra_2.lean | Set.IsRegularDomain、instIsRegularDomainEmpty | new | Manifold/RegularDomain | 否 | 正则域即散度定理积分域，依项目脚手架需重建 |
| Sec05_36/Definition_5_36_extra_3.lean | Manifold.IsRegularValue、IsRegularSublevelSet 等 | new | Manifold/RegularValue | 是 | 正则值概念填空白，iff 引理 sorry，设计需改 |
| Sec05_36/Proposition_5_46.lean | regular_domain_manifoldInterior_image_eq_interior 等 | new | Manifold/RegularDomain | 是 | 正则域内部/边界对应拓扑内部/边缘，证明全 sorry |
| Sec05_37/Problem_5_15.lean | transported_subset_chartedSpace、transported_subset_isManifold_top 等 | new | Manifold/StructureTransport | 否 | 结构沿同胚移植引理族已证可复用，反例部分教材性 |
| Sec05_37/Problem_5_19.lean | curve_velocity_mem_embedded_submanifold_tangent 等 | new | Manifold/Submanifold/Tangent | 否 | 曲线速度落入切子空间已证，半个文件是反例 |
| Sec05_37/Problem_5_4.lean | continuous_injective_interval_to_curve_manifold_isEmbedding 等 | new | Manifold/CurveEmbedding | 否 | 一维区域不变性辅助引理无 sorry，Mathlib 缺 |
| Sec05_37/Problem_5_5.lean | continuous_injective_real_to_curve_manifold_isEmbedding 等 | new | Manifold/CurveEmbedding | 否 | 实线入一维流形嵌入引理已证，宜与 5.4 并为一模块 |
| Sec05_37/Problem_5_6.lean | unitTangentBundle、unitTangentBundle_exists_isSmoothEmbedding 等 | new | TangentBundle/UnitTangentBundle | 是 | 单位切丛各处皆无，但主定理全 sorry，仅 API 种子 |
| Sec05_28/Proposition_5_1.lean | open_submanifold_isEmbeddedSubmanifold 等 | partial-dup | Manifold/Submanifold/Open | 是 | 部分重复 Mathlib of_opens，逆命题全 sorry 需推广 |
| Sec05_32/Definition_5_32_extra_2.lean | IsImmersedSubmanifold、IsWeaklyEmbeddedSubmanifold 等 | partial-dup | Manifold/Submanifold | 否 | 子流形谓词类填空白，API 需重做且一辅助重复 Mathlib |

</details>

<details><summary>跳过（34 项，绝大多数为 Mathlib 包装/recall 文件）</summary>

- Sec05_28/Corollary_5_6.lean — mathlib-dup — 一行复合既有引理
- Sec05_28/Definition_5_28_extra_2.lean — partial-dup — 薄命名缩写
- Sec05_28/Proposition_5_5.lean — mathlib-dup — 仅 #check 包装
- Sec05_29/Example_5_9.lean — partial-dup — 球面 API 重包装
- Sec05_29/Remark_5_29_extra_2.lean — new — 仅 sorry 语句备注
- Sec05_29/Remark_5_29_extra_3.lean — new — recall 交叉引用
- Sec05_30/Definition_5_30_extra_1.lean — mathlib-dup — recall 原像概念
- Sec05_30/Example_5_15.lean — mathlib-dup — 球面教学复述
- Sec05_30/Example_5_17.lean — new — 环面例全 sorry
- Sec05_31/Example_5_19.lean — new — 八字反例无 API
- Sec05_31/Example_5_25.lean — new — #check 加平凡推论
- Sec05_31/Example_5_26.lean — new — 八字脚手架含 sorry
- Sec05_31/Exercise_5_24.lean — new — 仅 recall/#check
- Sec05_32/Example_5_28.lean — new — 八字反例关键 sorry
- Sec05_32/Theorem_5_27.lean — mathlib-dup — recall 加一行特化
- Sec05_34/Notation_5_34_extra_1.lean — mathlib-dup — 纯记号引用
- Sec05_35/Definition_5_35_extra_4.lean — new — R² 专用脚手架
- Sec05_35/Example_5_45.lean — new — 单条平面曲线例
- Sec05_35/Exercise_5_36.lean — new — 纯 recall 复述
- Sec05_35/Exercise_5_42.lean — new — recall sorry 语句
- Sec05_36/Definition_5_36_extra_1.lean — mathlib-dup — #check 复述谓词
- Sec05_36/Exercise_5_50.lean — partial-dup — recall 重证组合
- Sec05_36/Exercise_5_52.lean — partial-dup — recall 再导出
- Sec05_36/Exercise_5_54.lean — partial-dup — recall 指针
- Sec05_36/Remark_5_36_extra_5.lean — partial-dup — 无声明备注
- Sec05_36/Theorem_5_53.lean — partial-dup — 一行包装且 sorry
- Sec05_37/Problem_5_1.lean — new — 具体习题无 API
- Sec05_37/Problem_5_10.lean — new — 三次曲线 17 sorry
- Sec05_37/Problem_5_11.lean — new — 具体零集全 sorry
- Sec05_37/Problem_5_12.lean — partial-dup — 新部分全 sorry
- Sec05_37/Problem_5_13.lean — new — 一次性反例含 sorry
- Sec05_37/Problem_5_20.lean — new — 八字反例无 API
- Sec05_37/Problem_5_7.lean — new — 单例分类含 sorry
- Sec05_37/Problem_5_9.lean — new — 单条 sorry 语句

</details>

## 小结

本章（第五章：子流形理论）是整个审计中移植价值最高的一章：嵌入/浸入子流形类、切片图卡判据、子流形切空间、局部定义映射与边界向量 API 共 18 个高价值文件，几乎全部为 Mathlib 空白且半数以上 sorry-free，可直接支撑 OpenGALib 的 GMT 与散度定理缺口。建议以 SliceCharts、Submanifold/Immersed+Embedded、Submanifold/TangentSpace 三条主线为骨架先移植无 sorry 文件，再用 medium 表中的 level-set 与 boundary 系列补全语句层。低价值条目以教材具体反例与 recall 脚手架为主，可整体跳过。
