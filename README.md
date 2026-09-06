# Normal-Locus Finite Étale 定理：证明与 Lean 验证

**以本仓库明确列出的 13 项外部几何结果为前提，NL 定理的组合证明已经完成，并通过 Lean 内核检查。**

这里公开完整的证明源码、外部输入、语义对照和验证程序。读者可以检查每一步用了什么，
也可以在自己的环境中重新运行验证。除本地检查外，同一形式化源码已在
[GitHub 的全新 Ubuntu 环境中完整复现成功](https://github.com/YukiRa1n/normal-locus-lean-certificate/actions/runs/34047288754)。

[实际 Lean 结论与完整证明](docs/target.md) · [13 项外部输入](docs/inputs.md) ·
[验证记录](verification/results.json) · [自动验证](https://github.com/YukiRa1n/normal-locus-lean-certificate/actions)

## 1. 证明了什么

**Normal-Locus Finite Étale Theorem（NL）。** 设 $F:\mathbb A^n_{\mathbb C}\to\mathbb A^n_{\mathbb C}$
是 Keller 多项式映射，即 Jacobian 行列式为非零常数。令 $S_F$ 为赋予约化结构的非适当集，
$S_F^{\mathrm{nor}}$ 为其正规轨迹。使用下文列出的外部结果，可得原映射的限制

$$
F^{-1}(S_F^{\mathrm{nor}})\longrightarrow S_F^{\mathrm{nor}}
$$

是**有限、étale、满射**的态射。

Lean 中的结论直接使用实际概形及其态射性质。下面两段取自
[Statement.lean](NormalLocus/Statement.lean)，验证程序逐字比较展示文本和源码：

```lean
def NormalLocusConclusion {n : ℕ} {K : Type*} [Field K] (F : PolynomialMap n K) : Prop :=
  ∃ U : (nonProperScheme F).Opens,
    (U : Set (nonProperScheme F)) = normalPoints (nonProperScheme F) ∧
    AlgebraicGeometry.IsFinite (restrictedMap F U) ∧ Etale (restrictedMap F U) ∧
    Surjective (restrictedMap F U)
```

```lean
def NormalLocusTheorem : Prop :=
  ∀ (n : ℕ) (F : PolynomialMap n ℂ), IsKeller F → NormalLocusConclusion F
```

[ConditionalNL.lean](NormalLocus/ConditionalNL.lean) 中已证明的定理具有以下类型：

```lean
NormalLocus.normal_locus_finite_etale_conditional :
  NormalLocus.External.Library → NormalLocus.NormalLocusTheorem
```

这精确表达了“**13 项输入成立，则 NL 成立**”。`def … : Prop` 定义命题，
而上述 `theorem` 提供已通过检查的证明项；[完整证明体](docs/target.md#完整组合证明)可直接查看。
外部结果本身及其引用转换是本证明公开保留的数学依据，尚未全部在本仓库内部证明。

## 2. 按 Lean 社区的五项准则核验

Lean 社区的 [《Did you prove it?》](https://leanprover-community.github.io/did_you_prove_it.html)
明确列出 **5 项验证准则**。本仓库逐项提供以下证据：

| 社区准则 | 本仓库的证据 |
|---|---|
| **1. 是规范、可复现的 Lean 工程吗？** | 提供完整项目，固定 Lean 4.28.0 和 mathlib 的完整提交；[版本清单](lake-manifest.json)与[源码摘要](manifest.json)可核对。 |
| **2. 工程能够编译吗？** | `lake build` 成功；[构建记录](verification/build.log)及[已成功的 CI](https://github.com/YukiRa1n/normal-locus-lean-certificate/actions/runs/34047288754)可查。 |
| **3. 主定理确实进入检查了吗？** | [构建入口](NormalLocus.lean)导入主定理模块；[审计程序](Audit.lean)检查它确实是 theorem，类型精确为 `Library → NormalLocusTheorem`。 |
| **4. 只依赖标准逻辑公理吗？** | 主定理的传递公理仅为 `propext`、`Classical.choice`、`Quot.sound`；[审计记录](verification/audit.log)和[重放记录](verification/replay.json)均可查看。 |
| **5. 证明的正是所声称的命题吗？** | 全部核心定义、13 项输入及最终目标公开展示；程序检查声明一致性，[语义审阅](docs/semantic-review.md)逐项对照其数学含义与引用。数学语义对应不是由编译自动认证的。 |

第五项尤其要求把前提说清楚：本仓库声称并证明的是 `Library → NL`。
13 项外部输入作为显式参数出现在定理类型中，不能因为公理检查通过就把这些参数省略。

这五项是社区验证准则。以通常对 Lean 逻辑与检查器的信任为基础，
它们把“有一段看似正确的代码”落实为可复核的形式化证明。
相关基础前提及更强核验方法见[官方验证指南](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
和[可靠性依据](docs/soundness.md)。

## 3. 外部输入是什么

这些输入是通用的几何与交换代数结果。每项的**完整 Lean 声明、使用的定义、原始引用**
都列在 [13 项输入](docs/inputs.md)，其展示代码由程序从实际源码提取并逐字核对。

| 编号 | 字段 | 数学输入 |
|---|---|---|
| 1 | `intersection` | 正规 Noether 整环的高度一局部化交公式 |
| 2 | `dimension` | 正规目标上有限支配映射的局部维数公式 |
| 3 | `normalization` | 有限正规化分量及其在正规开集上的同构 |
| 4 | `boundary` | 稠密仿射开集的边界为有限个素除子的并 |
| 5 | `etaleDivisors` | étale 逆像保持纯余维一除子分解 |
| 6 | `etaleNormal` | étale 态射保持正规性 |
| 7 | `abhyankar` | 正则除子点上，覆盖正规化的约化逆像局部不可约 |
| 8 | `divisorImage` | 正规目标上的有限支配映射将素除子映为素除子 |
| 9 | `divisorEquations` | 复仿射空间中的素除子有非恒定多项式方程 |
| 10 | `affineRegular` | 复仿射空间所有局部环正则 |
| 11 | `normalOpen` | 约化复代数概形的正规轨迹开 |
| 12 | `domainComponents` | 整环局部环对应唯一的过点不可约分量 |
| 13 | `regularOpen` | 开嵌入保持正则性 |

部分接口是原引用的推论形式。例如 Abhyankar 输入还包含在正则点附近缩小、
识别正规化、利用特征零得到 tame，再推出局部不可约的转换。
接受本证明的外部依据时，需要接受这些**精确输入及其转换**；
逐项论证见[语义审阅](docs/semantic-review.md#3-13-项外部输入逐项核对)。

<details>
<summary>查看实际 Lean 输入结构</summary>

以下两段是实际源码中的声明：

```lean
structure CoreGeometry : Prop where
  intersection : HeightOneIntersection
  dimension : FiniteLocalDimension
  normalization : NormalizationPieces
  boundary : AffineBoundaryDivisors
  etaleDivisors : EtalePullbackDivisors
  etaleNormal : EtalePreservesNormal
  abhyankar : AbhyankarLocalIrreducibility
```

```lean
structure Library : Prop extends CoreGeometry where
  divisorImage : FiniteDivisorImage
  divisorEquations : PolynomialPrimeDivisorEquation
  affineRegular : AffineSpaceRegular
  normalOpen : NormalLocusOpen
  domainComponents : DomainPointUniqueComponent
  regularOpen : RegularOpenImmersion
```

</details>

## 4. 这些输入怎样推出结论

形式化沿用文稿的主体路线：

1. 构造同一映射的有限正规完成，证明非适当集恰是边界的像。
2. 在正规轨迹的适当邻域内构造内部闭包除子和边界除子，利用 Abhyankar 的局部结论排除正则点上的碰撞。
3. 将剩余边界限制在余维至少二的部分，经正规化和仿射 Hartogs 消去边界，得到原限制态射有限。
4. 结合 étale 性、超曲面非遗漏和开闭像论证得到满射，再将局部结论粘合到整个正规轨迹。

Lean 检查的是这条推导的完整组合。有限性、étale 性和满射性均是 mathlib 的实际态射性质；
正规轨迹由实际局部环定义，限制态射来自原 F 的 pullback。
对象对照和形式化中的组织调整见[语义审阅](docs/semantic-review.md)。

因此，在所列外部输入成立、语义对应正确以及通常的 Lean 可信基础下，
**已检查的蕴含给出 NL 结论**。主体组合论证已有机器检查的证明项，其外部数学依赖由 `Library` 集中列明。

## 5. 验证实际做到了什么

除社区五项准则所要求的证据，本工程还完成了以下程序检查：

- **118 项定理的传递公理审计通过**，其中包括端到端主定理。
- **4 项错误证书测试正确拒绝**：错误目标、额外公理、`sorry`、额外前提。
- **75,402 个声明的新环境内核重放通过**：从主定理收集完整依赖，在空环境、trust level 0 重新检查。
- **展示一致性检查通过**：结果定义、13 项输入和 README 中的 Lean 声明与实际源码一致。

[验证摘要](verification/results.json)、[公理审计](verification/audit.log)、
[内核重放](verification/replay.log)和[检查程序](scripts/verify.py)全部公开。
重放使用同一官方内核，不是独立检查器；语义审阅与外部数学依据仍单独列明。

记录中的 `CONDITIONAL_VERIFIED` 表示上述组合验证完成；`MANUAL_REVIEW` 表示数学语义审阅；
`TRUST_ASSUMPTION` 表示基础信任。`unconditional_nl: INCOMPLETE` 专指尚未把所有外部输入
也在仓库内部证明，不否定已经通过的 `Library → NL` 组合证书。

## 6. 如何自行复现

安装 Git、Python 3.11 或更新版本，以及 [elan](https://github.com/leanprover/elan)。
运行：

```sh
git clone https://github.com/YukiRa1n/normal-locus-lean-certificate.git
cd normal-locus-lean-certificate
lake exe cache get
python scripts/verify.py
```

首次运行需要下载固定依赖，完整重放可能耗时较长。成功时程序输出 `CONDITIONAL_VERIFIED`。
每次 GitHub 推送也会触发[自动验证](.github/workflows/verify.yml)，并保存该次日志。

只检查文档可用 `python scripts/verify.py --check-docs`，该模式明确标记为静态检查。
`--require-complete` 则额外要求外部输入也全部消除；当前会返回退出码 2。
如需指定 Lake 可执行文件，可使用 `--lake /absolute/path/to/lake`。

进一步阅读：[冻结文稿](provenance/Normal_Loci_Keller_Maps_v1.tex)、
[输入与目标的语义对照](docs/semantic-review.md)、[逻辑可靠性及实现信任](docs/soundness.md)。

## 7. 工作分工

- **主体研究、定理构思、证明思路与原始文稿**：由 **GPT-5.6 Sol、GPT-5.6 Pro** 完成。
- **Lean 形式化与程序验证**：**GPT-6 Astra** 仅负责将既有证明形式化为 Lean，并实现相应的验证与审计程序。
