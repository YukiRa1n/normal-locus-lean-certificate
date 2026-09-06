"""Extract the displayed Lean declarations directly from the audited sources."""

from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]


def declaration(path: str, name: str) -> str:
    source = (ROOT / path).read_text(encoding="utf-8")
    match = re.search(
        rf"^(?:noncomputable )?(?:abbrev|def|structure|theorem) {re.escape(name)}\b",
        source, re.MULTILINE,
    )
    if match is None:
        raise ValueError(f"Declaration not found: {path}:{name}")
    end = source.find("\n\n", match.start())
    return source[match.start():end if end != -1 else len(source)].rstrip()


def code(path: str, name: str) -> str:
    return f"```lean\n{declaration(path, name)}\n```"


def input_document() -> str:
    inputs = json.loads((ROOT / "external_inputs.json").read_text(encoding="utf-8"))["inputs"]
    parts = [
        "# 13 项外部输入：实际 Lean 声明\n",
        "以下代码由 `scripts/snippets.py` 从被校验的源文件提取，验证程序逐字比较。"
        "每段是其所在命名空间中的声明片段；完整 imports、命名空间和变量环境以源文件为准。"
        "`def … : Prop` 定义一个命题，不是该命题的证明。13 项目前均为条件参数。\n",
        "数学解释及从原引用到接口的转换见 [语义审阅](semantic-review.md)。\n",
    ]
    for number, item in enumerate(inputs, 1):
        parts += [f"## {number}. `{item['field']}` / `{item['statement']}`\n",
                  f"[实际源码](../{item['file']})。TeX 锚点：" +
                  ", ".join(f"`{x}`" for x in item["tex_labels"]) + "。\n",
                  code(item["file"], item["statement"]) + "\n"]
        if item["sources"]:
            parts.append("原始来源：" + "、".join(
                f"[Stacks {url.rsplit('/', 1)[-1]}]({url})" for url in item["sources"]
            ) + "。\n")
        parts.append("当前状态：命题与调用已形式化；该通用输入的无条件证明未提供。\n")
    parts.append("## 输入中使用的项目定义\n")
    helpers = [
        ("NormalLocus/ExternalStatements.lean", "ComplexAlgebraic"),
        ("NormalLocus/ExternalStatements.lean", "globalToFunctionField"),
        ("NormalLocus/Statement.lean", "normalPoints"),
        ("NormalLocus/RegularPoints.lean", "regularPoints"),
        ("NormalLocus/BoundaryCollision.lean", "PrimeDivisor"),
        ("NormalLocus/DivisorClosure.lean", "IsDivisorUnion"),
        ("NormalLocus/NormalizedClosure.lean", "NormalizationPiece"),
        ("NormalLocus/ExternalGeometry.lean", "CoreGeometry"),
        ("NormalLocus/ExternalGeometry.lean", "Library"),
    ]
    for path, name in helpers:
        parts += [f"### `{name}`\n", code(path, name) + "\n"]
    return "\n".join(parts)


def target_block() -> str:
    items = [
        ("NormalLocus/Polynomial.lean", "PolynomialMap"),
        ("NormalLocus/Polynomial.lean", "jacobian"),
        ("NormalLocus/Polynomial.lean", "IsKeller"),
        ("NormalLocus/NonProper.lean", "nonProperLocus"),
        ("NormalLocus/Statement.lean", "nonProperIdeal"),
        ("NormalLocus/Statement.lean", "nonProperScheme"),
        ("NormalLocus/Statement.lean", "nonProperInclusion"),
        ("NormalLocus/Statement.lean", "normalPoints"),
        ("NormalLocus/Statement.lean", "restrictedMap"),
        ("NormalLocus/Statement.lean", "NormalLocusConclusion"),
        ("NormalLocus/Statement.lean", "NormalLocusTheorem"),
    ]
    return "\n\n".join(code(path, name) for path, name in items)


if __name__ == "__main__":
    (ROOT / "docs/inputs.md").write_text(input_document(), encoding="utf-8", newline="\n")
    (ROOT / "docs/target.md").write_text(
        "# 结果和全部核心定义\n\n"
        "以下是实际源文件中的声明片段，由验证程序逐字比对。完整上下文见对应 Lean 文件。\n\n"
        + target_block() + "\n\n## 完整组合证明\n\n"
        + code("NormalLocus/ConditionalNL.lean", "normal_locus_finite_etale_conditional") + "\n",
        encoding="utf-8", newline="\n",
    )
