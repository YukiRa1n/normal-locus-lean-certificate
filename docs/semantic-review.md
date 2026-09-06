# NL 条件式组合证明的语义核对

语义审阅日期：2026-09-06；独立仓库整理日期：2026-09-07。
范围：本仓库的 `NormalLocus` 源码、`provenance/Normal_Loci_Keller_Maps_v1.tex`
冻结文稿，以及外部输入对应的原始数学结果。

结论：条件式组合已经由 Lean 核验；目标忠于文稿。对 13 项输入的本次人工核对，
未发现把 NL 结论放进假设、缺少使输入成立的必要假设，或使用空壳几何定义的问题。
输入不是全部逐字翻译原引用；部分包含尚未机器证明的通用转换。
因此不能把此结论表述为“Lean 已核验原引用到 NL 的全部链条”。

## 1. 组合证书的核验范围

实际证书是：

```lean
normal_locus_finite_etale_conditional : External.Library → NormalLocusTheorem
```

整理前的完整组合验收包含 118 项定理审计，精确证书复核得到下面的状态。
独立仓库本次可复现检查的实际结果以
[results.json](../verification/results.json) 和 [audit.log](../verification/audit.log) 为准：

```text
EXTERNAL_INTERFACE_CHECKED: no Keller or NL-specific dependencies
CONDITIONAL_NL_VERIFIED: exact Library → NL target and standard axioms checked
FULL_NL_INCOMPLETE: no theorem certificate for the exact NL target
```

这里条件式检查成功不表示无条件完成；无条件完成检查明确报告未完成。
标准公理检查排除了 `sorryAx` 和项目自定义公理，但不会证明显式假设为真。
外部接口依赖检查可以排除指定的 NL 专用定义；它不是一般的语义正确性判定器，
也不证明 `External.Library` 有实例。后两件事不能由编译成功代替。

## 2. 目标逐项对应

| 文稿对象或结论 | 实际 Lean 表达 | 核对结果 |
|---|---|---|
| 复多项式映射 | `Fin n → MvPolynomial (Fin n) ℂ` | 系数域和多项式坐标均保留 |
| Keller 条件 | 形式偏导矩阵行列式等于 `C c`，且 `c ≠ 0` | 没有另加映射有限、单射或满射假设 |
| 非适当集 | 不存在使限制态射 proper 的目标 Zariski 开邻域 | 与 TeX 的 `def:nonproperness` 相同 |
| 约化闭子概形 S | 非适当闭集的消失理想的商环之 Spec | 已证明约化、闭嵌入及底层像等于该闭集 |
| 正规轨迹 | 实际 stalk 是整环且整闭 | 没有改成光滑轨迹，也没有换成 S 的正规化 |
| 正规开集的存在 | 存在开子概形 U，底层集合严格等于全部正规点 | 没有只取正规轨迹中的某个较小开集 |
| 原映射在该轨迹上的限制 | 原 `schemeMap F` 与 U 到环境的嵌入的 pullback 第二投影 | 没有换用有限完成的限制来充当原映射 |
| 有限、étale、满射 | mathlib 的概形态射性质，三项同时成立 | 不是仅有限纤维、一般拓扑性质或 `True` |

该目标包括所有自然数维数；零维情形是无害的额外情形，不弱化文稿结论。
目标的语义对照是人工检查；Lean 的精确类型检查保证证书证明的就是这个已检查的目标。

## 3. 13 项外部输入逐项核对

下表的“转换”属于输入的数学依据；未声称这些转换已被 Lean 证明。

| 字段 | 对应与必要转换 | 本次判断 |
|---|---|---|
| `intersection` | [0AVB](https://stacks.math.columbia.edu/tag/0AVB) 取有限反身模 M 为基环 R，得到高度一局部化交公式；再识别仿射概形的 stalk、分式域及全局截面嵌入 | 正规 Noether 整环假设保留；是几何转述 |
| `dimension` | 正规基整环的整扩张满足 [going down](https://stacks.math.columbia.edu/tag/037E)；配合 [10.112.7](https://stacks.math.columbia.edu/tag/00OG) 和有限映射零维纤维，得到各点 stalk 维数相等 | 不是仅由整体维数相等推局部维数相等；所需正规性已包含 |
| `normalization` | [0BXQ](https://stacks.math.columbia.edu/tag/0BXQ) 给有限正规化，[0357](https://stacks.math.columbia.edu/tag/0357) 给正规分量的开闭分解；结合正规化与开限制相容及 [0H7D](https://stacks.math.columbia.edu/tag/0H7D) 得在正规开集上的同构 | 分量仿射性、正规全局环、覆盖每一点、开集非空及开闭嵌入均在打包输入内 |
| `boundary` | [0BCV](https://stacks.math.columbia.edu/tag/0BCV) 给仿射稠密开集边界分量泛点的局部维数一；仿射环境分离，且仿射、局部 Noether 保证有限分量分解 | 假设足够；高度一到拓扑素除子的对应是转换 |
| `etaleDivisors` | étale 的平坦性、零维纤维及局部维数公式，把高度一保持到逆像分量；Noether 仿射性保证只有有限个分量 | 允许空逆像，未偷偷假设满射 |
| `etaleNormal` | étale 是 smooth 的特例，使用 [10.163.9](https://stacks.math.columbia.edu/tag/0336) 的正规性上升，再转为 stalk 表述 | 一般概形版本也成立，不依赖省略的 Noether 假设 |
| `abhyankar` | [0EYG](https://stacks.math.columbia.edu/tag/0EYG)、[0EYH](https://stacks.math.columbia.edu/tag/0EYH) 加下节列出的四段转换 | 是局部拓扑推论，不是原定理逐字表述；未发现丢失必要假设 |
| `divisorImage` | 有限支配、整概形及正规目标给高度相等，有限映射给像闭，从而高度一不可约闭集的像仍为高度一 | 正规目标已包含；不能只引用“有限映射保整体维数” |
| `divisorEquations` | 多项式 UFD 的高度一素理想由一个非零非单位生成；在域上的多项式环中，该生成元不可能为常数 | 是标准高度一主性推论，不含超曲面已被 F 命中的假设 |
| `affineRegular` | 域上的多项式环及其各素理想局部化正则；也可从仿射空间 smooth 和 [10.163.10](https://stacks.math.columbia.edu/tag/0336) 得到 | 对所有概形点陈述，未仅检查闭点 |
| `normalOpen` | 约化复代数概形的有限正规化，加相干商层的支撑闭性，给正规轨迹开性 | 有限型条件通过实际结构态射给出，未对任意约化概形断言 |
| `domainComponents` | [00ET](https://stacks.math.columbia.edu/tag/00ET) 给仿射谱中过点分量与局部环极小素理想对应；在仿射邻域应用并取全局闭包 | 整环只有一个极小素理想；局部 Noether 假设足够 |
| `regularOpen` | 开嵌入诱导 stalk 环同构，保留余切空间维数及 Krull 维数 | 是同构不变性，不含新的几何结论 |

`PrimeDivisor` 使用“极大真不可约闭子集”的拓扑定义。在这些输入的整概形环境中，
它对应通常的余维一素除子。`regularPoints` 使用实际局部环的余切空间维数等于
Krull 维数；Abhyankar 应用中的所有概形均为局部 Noether，因此该刻画与通常正则性一致。

## 4. Abhyankar 输入到底打包了什么

`AbhyankarLocalIrreducibility` 的假设没有直接写“有效 Cartier 除子”和 tame。
这不意味着可以无条件丢掉它们：从接口假设到原定理需要以下推导。

1. Z 是复有限型正规环境 Y 中的约化纯余维一闭子概形。在 Z 的正则点附近，
   利用正则轨迹开性缩小；正则环境局部阶乘，故该约化纯余维一子概形局部为
   有效 Cartier 除子。此处的“正规环境”由接口更强的全点正则性保证。
2. 有限支配映射 V → Y 的源是正规整概形。因此 V 是 Y 在其函数域扩张中的正规化。
   接口还要求避开 Z 的每个目标开集上的限制为 étale，故补集上是有限 étale 覆盖。
3. Y 的复代数结构使余维一点的剩余域具有特征零；有限函数域扩张可分，
   [09E9](https://stacks.math.columbia.edu/tag/09E9) 的 tame 条件满足。
4. [0EYH](https://stacks.math.columbia.edu/tag/0EYH) 给约化逆像除子的正则性。
   正则 Noether 概形局部不可约，故可选 V 中的 Zariski 开邻域 W，
   使逆像除子的底层集合与 W 的交不可约。这正是接口的结论。

这些推导在普通数学层面说明接口是原结果在当前假设下的推论。
它们仍在外部边界内，尤其不能把“Kummer 局部表示存在性”算作已由当前 Lean 工程证明。
Lean 已证明的是在这个局部不可约性结论下，两个不同素除子不能相交的后续碰撞排除。

## 5. 能支持的结论

- 可以说：已核验从 13 项精确外部命题到忠实 NL 目标的端到端组合推导。
- 可以说：本次人工逐项对照未发现输入偷换或必要假设缺失，主要推导路线保留。
- 不能说：原始引用到这些接口的所有转换已经机器核验，或无条件 NL 已形式化完成。
- 不能仅凭此证书宣布整份 TeX 的所有定理、导子推论和所有文字表述都已通过 Lean 检查。

独立仓库保留 TeX 数学正文和数学 Lean 模块，不改变 NL 无条件形式化尚未完成的状态，
也不声称证明 JC2。这里只审阅 NL 的条件式组合及其输入语义。
