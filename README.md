# NL 定理的 Lean 条件式证明与可信性说明

本仓库给出 **Normal-Locus Finite Étale Theorem（NL）** 的可检查组合证明：
对复多项式 Keller 映射 F，非适当集的正规轨迹上的原映射限制是有限、étale、满射。
组合证明以 **13 项明确列出的通用几何结果**为输入。本文依次展示结果、输入、
语义对应与可靠性依据，并用程序验证其中可执行的条件。

**当前证书是 `External.Library → NormalLocusTheorem`。13 项输入本身的无条件证明
尚未提供；本仓库的通过状态表示条件式组合通过，不表示无条件 NL 已完成。**

## 1. 先看实际证明的结果

下面两段直接取自 [Statement.lean](NormalLocus/Statement.lean)，验证程序检查 README
中的代码与源文件逐字一致：

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

[ConditionalNL.lean](NormalLocus/ConditionalNL.lean) 中实际定理的类型为：

```lean
NormalLocus.normal_locus_finite_etale_conditional :
  NormalLocus.External.Library → NormalLocus.NormalLocusTheorem
```

这里最后一段展示声明的类型，完整证明体和全部核心定义见
[结果及实际 Lean 证明](docs/target.md)。`def … : Prop` 只是命题的定义；
真正的证明是上述 `theorem` 声明。可检查源码总共保留 35 个数学模块。

| 数学含义 | 实际实现 | 防止的语义偏移 |
|---|---|---|
| 复多项式映射 | `Fin n → MvPolynomial (Fin n) ℂ` | 不是任意点映射 |
| Keller 条件 | 形式偏导矩阵的行列式等于非零常数多项式 | 不额外假设 F 有限或满射 |
| 非适当集 S | 没有使 F 的限制 proper 的目标 Zariski 开邻域；再取消失理想的商环 Spec | 与文稿的定义相同，且已证明底层集合相符及约化性 |
| 正规轨迹 | 实际 stalk 是整环且整闭 | 不换成光滑轨迹或 S 的正规化 |
| 轨迹范围 | U 的点集等于 S 的全部正规点 | 不缩小为某个容易证明的开子集 |
| 限制态射 | 原 F 与 U 的嵌入的 pullback 第二投影 | 不用有限完成的态射替代原 F |
| 结论 | mathlib 的 `IsFinite`、`Etale`、`Surjective` | 不用有限纤维或占位谓词替代 |

## 2. 再看全部输入

13 项输入的组织方式是实际源码中的以下两个结构：

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

**每一项的完整 Lean 声明、辅助定义及引用均展示在 [13 项输入](docs/inputs.md)。**
该文档从实际源文件生成，程序逐字检查，因而不会只展示一个看似合理的手写近似版本。

| 编号 | 字段 | 数学输入 |
|---|---|---|
| 1 | `intersection` | 正规 Noether 整环的高度一局部化交公式 |
| 2 | `dimension` | 正规目标上有限支配映射的 stalk 维数公式 |
| 3 | `normalization` | 约化复仿射概形的有限正规化分量及正规开集上的同构 |
| 4 | `boundary` | 稠密仿射开集的边界为有限个素除子的并 |
| 5 | `etaleDivisors` | étale 逆像保持纯余维一除子分解 |
| 6 | `etaleNormal` | étale 态射保持正规性 |
| 7 | `abhyankar` | 正则除子点上，有限 tame 覆盖正规化的约化逆像局部不可约 |
| 8 | `divisorImage` | 正规目标上的有限支配映射将素除子映为素除子 |
| 9 | `divisorEquations` | 复仿射空间中的素除子有非恒定多项式方程 |
| 10 | `affineRegular` | 复仿射空间所有局部环正则 |
| 11 | `normalOpen` | 约化复代数概形的正规轨迹开 |
| 12 | `domainComponents` | 整环 stalk 对应唯一的过点不可约分量 |
| 13 | `regularOpen` | 开嵌入保持局部环正则性 |

这些输入都使用实际环、概形、态射、局部环和拓扑。它们没有被声明为项目公理，
而是证书的显式参数；这让证明依赖可以被看见，并不使输入自动成立。

本次人工对照未发现输入或目标偷换，但“如实翻译”不能仅由编译验证。
部分接口是引用结果的推论形式。例如 Abhyankar 接口把缩小为正则 Cartier 除子、
正规化识别、特征零 tame 和正则性推出局部不可约打包在输入中。
这些转换的依据和所需假设逐项写在 [语义审阅](docs/semantic-review.md)，仍属于外部数学边界。

## 3. 为什么这样的证书可以支持数学结论

这里使用的是**类型论的语义可靠性（soundness）**，不是“代码运行没有报错就是真的”。
Carneiro 的 *The Type Theory of Lean*（2019）在 Soundness 一节的 `thm:sound`
给出：在其形式系统及所需集合论宇宙假设下，合法类型推导的解释确实属于类型的解释。
对命题而言，这把合法证明项连接到语义真值。
参见[作者发布的原文源码](https://github.com/digama0/lean-type-theory/blob/v1.0/soundness.tex)。

应用到本项目，可得到以下**相对可信性归约**：

> 若所用检查器正确实现了适用于这些证明项的可靠逻辑，审阅的 Lean 定义忠实表达
> 文稿，且 13 项精确输入成立，那么通过检查的 `Library → NL` 证明给出文稿中的 NL。

论证只有三步：可靠性使已检查的蕴含成立；外部定理及其接口转换使前件成立；
蕴含消去得到 NL，再通过语义对应回到文稿。组合层的证明工作由 Lean 检查，
外部数学依据仍完整公开。

**不能把上述 2019 年抽象类型论结果直接称作 Lean 4.28.0 二进制已经被证明正确。**
程序不能证明不可达基数假设、全部翻译正确性或自身实现绝无缺陷。
[可靠性依据详解](docs/soundness.md)分别说明了抽象逻辑、具体检查器和数学翻译三层，
并引用 Lean 官方验证指南；同时记录本项目尚未进行独立检查器验证的限制。

## 4. 把可执行的条件落实为检查

运行 `python scripts/verify.py`，程序依次执行：

| 检查 | 接受条件 |
|---|---|
| 版本与源码 | 固定 Lean 4.28.0、mathlib 完整 commit；核对冻结源文件 SHA-256 和集合 |
| 展示一致性 | README、目标文档、13 项输入文档与实际 Lean 声明一致 |
| 输入边界 | 登记与 `Library` 的 13 个字段完全相符；递归排除指定 NL 专用定义混入接口 |
| 构建 | 所有项目模块构建成功 |
| 目标检查 | 证书必须是 theorem，类型精确为 `Library → NormalLocusTheorem` |
| 公理审计 | 118 项登记定理的传递公理仅允许 `propext`、`Classical.choice`、`Quot.sound` |
| 负向测试 | 错目标、额外公理、`sorry`、额外前提均必须被拒绝 |
| 新环境重放 | 从主定理收集完整声明依赖闭包，在空环境、trust level 0 重新送入官方内核 |

重放程序还拒绝证明闭包中的 unsafe / partial 声明和白名单之外的公理。
它使用本版本内置检查器的 `Environment.replay'`，会重新生成并比对归纳类型构造子及递归器。
它不是独立检查器，也不单独验证检查器的实现正确性。

结果保存在 [verification/results.json](verification/results.json)，详细日志位于
[verification](verification/)。程序把不同性质的结论保留为不同状态：

- `CONDITIONAL_VERIFIED`：本次所有可执行检查通过。
- `MANUAL_REVIEW`：输入和目标的数学语义由逐项审阅支持。
- `TRUST_ASSUMPTION`：逻辑可靠性及检查器正确实现仍是基础前提。
- `INCOMPLETE`：13 项输入未全部证明，无条件 NL 证书不存在。

这避免把程序可检查的条件、数学前提和基础信任混写成一个“全部已证”的标志。

## 5. 复现

安装 Git、Python 3.11 或更新版本，以及 [elan](https://github.com/leanprover/elan)。
在仓库根目录运行：

```sh
git clone https://github.com/YukiRa1n/normal-locus-lean-certificate.git
cd normal-locus-lean-certificate
lake exe cache get
python scripts/verify.py
```

首次运行需要下载固定依赖和缓存，完整重放可能耗时较长。
验证不依赖原研究目录，也不需要作者的本地 `.olean` 文件。
如果 elan 代理不可用，可用 `--lake /absolute/path/to/lake` 指定所需版本的 Lake。

仅检查文档及冻结文件：

```sh
python scripts/verify.py --check-docs
```

该模式明确输出 `STATIC_ONLY_NOT_PROOF_CHECK`，不产生证明通过记录。
如要求无条件 NL 验收，可运行 `python scripts/verify.py --require-complete`；
当前即使条件式检查成功，它仍返回退出码 2。
CI 自动运行完整条件式检查并保存当次日志；提交中的静态日志不代替读者重新运行。

## 6. 文件与审阅边界

- [数学证明](NormalLocus/)及[组合入口](NormalLocus/ConditionalNL.lean)：实际 Lean 源码。
- [全部结果定义与证明体](docs/target.md)、[13 项输入](docs/inputs.md)：程序核对的展示稿。
- [语义审阅](docs/semantic-review.md)：逐项说明量词、假设、对象及引用转换。
- [可靠性依据](docs/soundness.md)：准确引用 soundness，并列出不能自动消除的前提。
- [冻结文稿](provenance/Normal_Loci_Keller_Maps_v1.tex)、[文件清单](manifest.json)：固定所审阅对象。
- [验证程序](scripts/verify.py)、[重放程序](scripts/Replay.lean)：可复现的接受条件。

本仓库只认证所展示的条件式 NL 组合，不宣称证明 Jacobian 猜想，也不宣称
整份原稿中的所有推论都已形式化。更新定义、输入或目标时，必须重新审阅其含义，
再更新冻结清单并重新验证；改写哈希不是数学审阅。
